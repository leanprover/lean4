// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Let
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.BuiltinDo.Basic import Lean.Elab.Do.PatternVar
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_throwUnlessMutVarsDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetRecDeclsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "Impossible case in elabDoLetOrReassign. This is an elaborator bug.\n"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__7_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__20 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__26_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__27 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__27_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__29_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__30 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__31_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__32 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__33 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__30_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__33_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__34 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__27_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__34_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__38 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__38_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__40 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__40_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__40_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__42 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__42_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "failed to infer `"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` declaration type"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "failed to infer universe levels in `"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "let_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "waitIfTypeMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "wait_if_type_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letEqnsDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 210, 72, 51, 179, 245, 26, 94)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(221, 9, 221, 202, 9, 173, 58, 127)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 25, 49, 206, 109, 94, 77, 137)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__7;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "let body of "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "reassignment with `|` (i.e., \"else clause\") is not supported"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mut"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__x"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__5_value),LEAN_SCALAR_PTR_LITERAL(238, 215, 60, 46, 39, 217, 189, 106)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoLet"};
static const lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 0, 15, 120, 200, 84, 91, 220)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoHave"};
static const lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 115, 123, 116, 44, 216, 133, 101)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "letrec"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "let rec body of group "};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetRec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetRec___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoLetRec"};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 245, 136, 148, 64, 2, 202, 185)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoReassign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__2_value;
static const lean_array_object l_Lean_Elab_Do_elabDoReassign___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoReassign"};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 53, 237, 208, 54, 227, 67, 171)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetElse___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__11;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__10_value),LEAN_SCALAR_PTR_LITERAL(182, 237, 62, 79, 212, 57, 236, 253)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__13_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__10_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PUnit.unit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetElse___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__18;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__19_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__23 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__24 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__22_value),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__24_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__25 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabDoLetElse"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 42, 180, 235, 57, 50, 131, 26)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoLetArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 6, 18, 178, 201, 235, 246, 214)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabDoReassignArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 247, 22, 101, 121, 153, 219, 18)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Do_LetOrReassign_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
lean_object* v_mutTk_x3f_9_; lean_object* v___x_10_; 
v_mutTk_x3f_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_mutTk_x3f_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_mutTk_x3f_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Do_LetOrReassign_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim___redArg(lean_object* v_t_23_, lean_object* v_let_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_23_, v_let_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_let_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_27_, v_let_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim___redArg(lean_object* v_t_31_, lean_object* v_have_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_31_, v_have_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_have_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_35_, v_have_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim___redArg(lean_object* v_t_39_, lean_object* v_reassign_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_39_, v_reassign_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_reassign_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_43_, v_reassign_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(lean_object* v_letOrReassign_47_){
_start:
{
if (lean_obj_tag(v_letOrReassign_47_) == 0)
{
lean_object* v_mutTk_x3f_48_; 
v_mutTk_x3f_48_ = lean_ctor_get(v_letOrReassign_47_, 0);
lean_inc(v_mutTk_x3f_48_);
return v_mutTk_x3f_48_;
}
else
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f___boxed(lean_object* v_letOrReassign_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_50_);
lean_dec(v_letOrReassign_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object* v_letOrReassign_52_, lean_object* v_vars_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
if (lean_obj_tag(v_letOrReassign_52_) == 2)
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Do_throwUnlessMutVarsDeclared(v_vars_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v_vars_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object* v_letOrReassign_64_, lean_object* v_vars_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_64_, v_vars_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec_ref(v_vars_65_);
lean_dec(v_letOrReassign_64_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(lean_object* v_t_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; lean_object* v_infoState_79_; uint8_t v_enabled_80_; 
v___x_78_ = lean_st_ref_get(v___y_76_);
v_infoState_79_ = lean_ctor_get(v___x_78_, 7);
lean_inc_ref(v_infoState_79_);
lean_dec(v___x_78_);
v_enabled_80_ = lean_ctor_get_uint8(v_infoState_79_, sizeof(void*)*3);
lean_dec_ref(v_infoState_79_);
if (v_enabled_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_t_75_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v_infoState_84_; lean_object* v_env_85_; lean_object* v_nextMacroScope_86_; lean_object* v_ngen_87_; lean_object* v_auxDeclNGen_88_; lean_object* v_traceState_89_; lean_object* v_cache_90_; lean_object* v_messages_91_; lean_object* v_snapshotTasks_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_114_; 
v___x_83_ = lean_st_ref_take(v___y_76_);
v_infoState_84_ = lean_ctor_get(v___x_83_, 7);
v_env_85_ = lean_ctor_get(v___x_83_, 0);
v_nextMacroScope_86_ = lean_ctor_get(v___x_83_, 1);
v_ngen_87_ = lean_ctor_get(v___x_83_, 2);
v_auxDeclNGen_88_ = lean_ctor_get(v___x_83_, 3);
v_traceState_89_ = lean_ctor_get(v___x_83_, 4);
v_cache_90_ = lean_ctor_get(v___x_83_, 5);
v_messages_91_ = lean_ctor_get(v___x_83_, 6);
v_snapshotTasks_92_ = lean_ctor_get(v___x_83_, 8);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_114_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_114_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_snapshotTasks_92_);
lean_inc(v_infoState_84_);
lean_inc(v_messages_91_);
lean_inc(v_cache_90_);
lean_inc(v_traceState_89_);
lean_inc(v_auxDeclNGen_88_);
lean_inc(v_ngen_87_);
lean_inc(v_nextMacroScope_86_);
lean_inc(v_env_85_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_114_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
uint8_t v_enabled_96_; lean_object* v_assignment_97_; lean_object* v_lazyAssignment_98_; lean_object* v_trees_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_113_; 
v_enabled_96_ = lean_ctor_get_uint8(v_infoState_84_, sizeof(void*)*3);
v_assignment_97_ = lean_ctor_get(v_infoState_84_, 0);
v_lazyAssignment_98_ = lean_ctor_get(v_infoState_84_, 1);
v_trees_99_ = lean_ctor_get(v_infoState_84_, 2);
v_isSharedCheck_113_ = !lean_is_exclusive(v_infoState_84_);
if (v_isSharedCheck_113_ == 0)
{
v___x_101_ = v_infoState_84_;
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_trees_99_);
lean_inc(v_lazyAssignment_98_);
lean_inc(v_assignment_97_);
lean_dec(v_infoState_84_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_PersistentArray_push___redArg(v_trees_99_, v_t_75_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 2, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_assignment_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_lazyAssignment_98_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v___x_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_112_, sizeof(void*)*3, v_enabled_96_);
v___x_105_ = v_reuseFailAlloc_112_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_107_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 7, v___x_105_);
v___x_107_ = v___x_94_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_env_85_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_nextMacroScope_86_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v_ngen_87_);
lean_ctor_set(v_reuseFailAlloc_111_, 3, v_auxDeclNGen_88_);
lean_ctor_set(v_reuseFailAlloc_111_, 4, v_traceState_89_);
lean_ctor_set(v_reuseFailAlloc_111_, 5, v_cache_90_);
lean_ctor_set(v_reuseFailAlloc_111_, 6, v_messages_91_);
lean_ctor_set(v_reuseFailAlloc_111_, 7, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_111_, 8, v_snapshotTasks_92_);
v___x_107_ = v_reuseFailAlloc_111_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_st_ref_set(v___y_76_, v___x_107_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg___boxed(lean_object* v_t_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v_t_115_, v___y_116_);
lean_dec(v___y_116_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(32u);
v___x_120_ = lean_mk_empty_array_with_capacity(v___x_119_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1(void){
_start:
{
size_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_122_ = ((size_t)5ULL);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_unsigned_to_nat(32u);
v___x_125_ = lean_mk_empty_array_with_capacity(v___x_124_);
v___x_126_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0);
v___x_127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_123_);
lean_ctor_set(v___x_127_, 3, v___x_123_);
lean_ctor_set_usize(v___x_127_, 4, v___x_122_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(lean_object* v_t_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v_infoState_138_; uint8_t v_enabled_139_; 
v___x_137_ = lean_st_ref_get(v___y_135_);
v_infoState_138_ = lean_ctor_get(v___x_137_, 7);
lean_inc_ref(v_infoState_138_);
lean_dec(v___x_137_);
v_enabled_139_ = lean_ctor_get_uint8(v_infoState_138_, sizeof(void*)*3);
lean_dec_ref(v_infoState_138_);
if (v_enabled_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref(v_t_128_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v_t_128_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v___x_143_, v___y_135_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___boxed(lean_object* v_t_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v_t_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_box(0);
return v___x_157_;
}
else
{
lean_object* v_key_158_; lean_object* v_value_159_; lean_object* v_tail_160_; uint8_t v___x_161_; 
v_key_158_ = lean_ctor_get(v_x_156_, 0);
v_value_159_ = lean_ctor_get(v_x_156_, 1);
v_tail_160_ = lean_ctor_get(v_x_156_, 2);
v___x_161_ = lean_name_eq(v_key_158_, v_a_155_);
if (v___x_161_ == 0)
{
v_x_156_ = v_tail_160_;
goto _start;
}
else
{
lean_object* v___x_163_; 
lean_inc(v_value_159_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_value_159_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_164_, v_x_165_);
lean_dec(v_x_165_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_167_; uint64_t v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(1723u);
v___x_168_ = lean_uint64_of_nat(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(lean_object* v_m_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_buckets_171_; lean_object* v___x_172_; uint64_t v___y_174_; 
v_buckets_171_ = lean_ctor_get(v_m_169_, 1);
v___x_172_ = lean_array_get_size(v_buckets_171_);
if (lean_obj_tag(v_a_170_) == 0)
{
uint64_t v___x_188_; 
v___x_188_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0);
v___y_174_ = v___x_188_;
goto v___jp_173_;
}
else
{
uint64_t v_hash_189_; 
v_hash_189_ = lean_ctor_get_uint64(v_a_170_, sizeof(void*)*2);
v___y_174_ = v_hash_189_;
goto v___jp_173_;
}
v___jp_173_:
{
uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v_fold_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_175_ = 32ULL;
v___x_176_ = lean_uint64_shift_right(v___y_174_, v___x_175_);
v_fold_177_ = lean_uint64_xor(v___y_174_, v___x_176_);
v___x_178_ = 16ULL;
v___x_179_ = lean_uint64_shift_right(v_fold_177_, v___x_178_);
v___x_180_ = lean_uint64_xor(v_fold_177_, v___x_179_);
v___x_181_ = lean_uint64_to_usize(v___x_180_);
v___x_182_ = lean_usize_of_nat(v___x_172_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_sub(v___x_182_, v___x_183_);
v___x_185_ = lean_usize_land(v___x_181_, v___x_184_);
v___x_186_ = lean_array_uget_borrowed(v_buckets_171_, v___x_185_);
v___x_187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_170_, v___x_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___boxed(lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v_m_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_m_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(lean_object* v___x_193_, lean_object* v_as_194_, size_t v_sz_195_, size_t v_i_196_, lean_object* v_b_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_a_207_; uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_lt(v_i_196_, v_sz_195_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v_b_197_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v_a_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = lean_box(0);
v_a_214_ = lean_array_uget_borrowed(v_as_194_, v_i_196_);
v___x_215_ = l_Lean_TSyntax_getId(v_a_214_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_193_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_238_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_238_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_238_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_val_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_238_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; 
lean_inc(v___x_215_);
v___x_221_ = l_Lean_Meta_getFVarFromUserName(v___x_215_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
v___x_223_ = l_Lean_Expr_fvarId_x21(v_a_222_);
lean_dec(v_a_222_);
v___x_224_ = l_Lean_instBEqFVarId_beq(v___x_223_, v_val_217_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_215_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v_val_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 11);
lean_ctor_set(v___x_219_, 0, v___x_225_);
v___x_227_ = v___x_219_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v___x_227_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_dec_ref(v___x_228_);
v_a_207_ = v___x_213_;
goto v___jp_206_;
}
else
{
return v___x_228_;
}
}
}
else
{
lean_dec(v___x_223_);
lean_del_object(v___x_219_);
lean_dec(v_val_217_);
lean_dec(v___x_215_);
v_a_207_ = v___x_213_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_del_object(v___x_219_);
lean_dec(v_val_217_);
lean_dec(v___x_215_);
v_a_230_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_221_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_221_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_dec(v___x_216_);
lean_dec(v___x_215_);
v_a_207_ = v___x_213_;
goto v___jp_206_;
}
}
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_196_, v___x_208_);
v_i_196_ = v___x_209_;
v_b_197_ = v_a_207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2___boxed(lean_object* v___x_239_, lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
size_t v_sz_boxed_252_; size_t v_i_boxed_253_; lean_object* v_res_254_; 
v_sz_boxed_252_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_253_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(v___x_239_, v_as_240_, v_sz_boxed_252_, v_i_boxed_253_, v_b_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec_ref(v_as_240_);
lean_dec_ref(v___x_239_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_255_, lean_object* v_vars_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
if (lean_obj_tag(v_letOrReassign_255_) == 2)
{
lean_object* v_mutVarDefs_265_; lean_object* v___x_266_; size_t v_sz_267_; size_t v___x_268_; lean_object* v___x_269_; 
v_mutVarDefs_265_ = lean_ctor_get(v_a_257_, 2);
v___x_266_ = lean_box(0);
v_sz_267_ = lean_array_size(v_vars_256_);
v___x_268_ = ((size_t)0ULL);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(v_mutVarDefs_265_, v_vars_256_, v_sz_267_, v___x_268_, v___x_266_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_277_);
v___x_271_ = v___x_269_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___x_269_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_266_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_266_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
return v___x_269_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_280_, lean_object* v_vars_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_280_, v_vars_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec_ref(v_vars_281_);
lean_dec(v_letOrReassign_280_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_00_u03b2_291_, lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v_m_292_, v_a_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_00_u03b2_295_, lean_object* v_m_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_00_u03b2_295_, v_m_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_m_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2(lean_object* v_t_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v_t_299_, v___y_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___boxed(lean_object* v_t_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2(v_t_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_320_, v_x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_a_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(v_00_u03b2_323_, v_a_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(lean_object* v_elabBody_327_, lean_object* v_body_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_apply_8(v_elabBody_327_, v_body_328_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object* v_elabBody_338_, lean_object* v_body_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(v_elabBody_338_, v_body_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec_ref(v___y_340_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(lean_object* v_letOrReassign_349_, lean_object* v_vars_350_, lean_object* v_k_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_349_, v_vars_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_361_; 
lean_dec_ref(v___x_360_);
v___x_361_ = lean_apply_8(v_k_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_k_351_);
v_a_362_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed(lean_object* v_letOrReassign_370_, lean_object* v_vars_371_, lean_object* v_k_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(v_letOrReassign_370_, v_vars_371_, v_k_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec_ref(v_vars_371_);
lean_dec(v_letOrReassign_370_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith(lean_object* v_hint_382_, lean_object* v_letOrReassign_383_, lean_object* v_vars_384_, lean_object* v_k_385_, lean_object* v_elabBody_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___f_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v_elabCont_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___f_395_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed), 10, 1);
lean_closure_set(v___f_395_, 0, v_elabBody_386_);
lean_inc_ref(v_vars_384_);
lean_inc(v_letOrReassign_383_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_396_, 0, v_letOrReassign_383_);
lean_closure_set(v___f_396_, 1, v_vars_384_);
lean_closure_set(v___f_396_, 2, v_k_385_);
v___x_397_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_383_);
lean_dec(v_letOrReassign_383_);
v_elabCont_398_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVars_x3f___boxed), 12, 4);
lean_closure_set(v_elabCont_398_, 0, lean_box(0));
lean_closure_set(v_elabCont_398_, 1, v___x_397_);
lean_closure_set(v_elabCont_398_, 2, v_vars_384_);
lean_closure_set(v_elabCont_398_, 3, v___f_396_);
v___x_399_ = lean_box(0);
v___x_400_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v_hint_382_, v_elabCont_398_, v___f_395_, v___x_399_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___boxed(lean_object* v_hint_401_, lean_object* v_letOrReassign_402_, lean_object* v_vars_403_, lean_object* v_k_404_, lean_object* v_elabBody_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Do_elabDoLetOrReassignWith(v_hint_401_, v_letOrReassign_402_, v_vars_403_, v_k_404_, v_elabBody_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_415_, lean_object* v_vars_416_, lean_object* v_k_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_inc_ref(v_vars_416_);
lean_inc(v_letOrReassign_415_);
v___f_426_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_426_, 0, v_letOrReassign_415_);
lean_closure_set(v___f_426_, 1, v_vars_416_);
lean_closure_set(v___f_426_, 2, v_k_417_);
v___x_427_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_415_);
lean_dec(v_letOrReassign_415_);
v___x_428_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_427_, v_vars_416_, v___f_426_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_429_, lean_object* v_vars_430_, lean_object* v_k_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_429_, v_vars_430_, v_k_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_459_, lean_object* v_a_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_469_, lean_object* v_a_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_469_, v_a_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v___x_487_; lean_object* v_mctx_488_; lean_object* v_lctx_489_; lean_object* v_options_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_485_ = lean_st_ref_get(v___y_483_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_485_);
v___x_487_ = lean_st_ref_get(v___y_481_);
v_mctx_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_ref(v_mctx_488_);
lean_dec(v___x_487_);
v_lctx_489_ = lean_ctor_get(v___y_480_, 2);
v_options_490_ = lean_ctor_get(v___y_482_, 2);
lean_inc_ref(v_options_490_);
lean_inc_ref(v_lctx_489_);
v___x_491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_491_, 0, v_env_486_);
lean_ctor_set(v___x_491_, 1, v_mctx_488_);
lean_ctor_set(v___x_491_, 2, v_lctx_489_);
lean_ctor_set(v___x_491_, 3, v_options_490_);
v___x_492_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_msgData_479_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_500_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_box(1);
v___x_502_ = l_Lean_MessageData_ofFormat(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2));
v___x_507_ = l_Lean_MessageData_ofFormat(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
return v_x_508_;
}
else
{
lean_object* v_head_510_; lean_object* v_tail_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_533_; 
v_head_510_ = lean_ctor_get(v_x_509_, 0);
v_tail_511_ = lean_ctor_get(v_x_509_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_533_ == 0)
{
v___x_513_ = v_x_509_;
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_tail_511_);
lean_inc(v_head_510_);
lean_dec(v_x_509_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_before_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_531_; 
v_before_515_ = lean_ctor_get(v_head_510_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_head_510_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_head_510_, 1);
lean_dec(v_unused_532_);
v___x_517_ = v_head_510_;
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_before_515_);
lean_dec(v_head_510_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 7);
lean_ctor_set(v___x_517_, 1, v___x_519_);
lean_ctor_set(v___x_517_, 0, v_x_508_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_x_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_530_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 7);
lean_ctor_set(v___x_513_, 1, v___x_522_);
lean_ctor_set(v___x_513_, 0, v___x_521_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_529_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = l_Lean_MessageData_ofSyntax(v_before_515_);
v___x_526_ = l_Lean_indentD(v___x_525_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v_x_508_ = v___x_527_;
v_x_509_ = v_tail_511_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object* v_opts_534_, lean_object* v_opt_535_){
_start:
{
lean_object* v_name_536_; lean_object* v_defValue_537_; lean_object* v_map_538_; lean_object* v___x_539_; 
v_name_536_ = lean_ctor_get(v_opt_535_, 0);
v_defValue_537_ = lean_ctor_get(v_opt_535_, 1);
v_map_538_ = lean_ctor_get(v_opts_534_, 0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_538_, v_name_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_defValue_537_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; 
v_val_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v___x_539_);
if (lean_obj_tag(v_val_541_) == 1)
{
uint8_t v_v_542_; 
v_v_542_ = lean_ctor_get_uint8(v_val_541_, 0);
lean_dec_ref(v_val_541_);
return v_v_542_;
}
else
{
uint8_t v___x_543_; 
lean_dec(v_val_541_);
v___x_543_ = lean_unbox(v_defValue_537_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_544_, lean_object* v_opt_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_opts_544_, v_opt_545_);
lean_dec_ref(v_opt_545_);
lean_dec_ref(v_opts_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1));
v___x_552_ = l_Lean_MessageData_ofFormat(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object* v_msgData_553_, lean_object* v_macroStack_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_options_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_options_557_ = lean_ctor_get(v___y_555_, 2);
v___x_558_ = l_Lean_Elab_pp_macroStack;
v___x_559_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec(v_macroStack_554_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_msgData_553_);
return v___x_560_;
}
else
{
if (lean_obj_tag(v_macroStack_554_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_msgData_553_);
return v___x_561_;
}
else
{
lean_object* v_head_562_; lean_object* v_after_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_578_; 
v_head_562_ = lean_ctor_get(v_macroStack_554_, 0);
lean_inc(v_head_562_);
v_after_563_ = lean_ctor_get(v_head_562_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_head_562_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_head_562_, 0);
lean_dec(v_unused_579_);
v___x_565_ = v_head_562_;
v_isShared_566_ = v_isSharedCheck_578_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_after_563_);
lean_dec(v_head_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_578_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 7);
lean_ctor_set(v___x_565_, 1, v___x_567_);
lean_ctor_set(v___x_565_, 0, v_msgData_553_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_msgData_553_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_577_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_msgData_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_570_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_MessageData_ofSyntax(v_after_563_);
v___x_573_ = l_Lean_indentD(v___x_572_);
v_msgData_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_574_, 0, v___x_571_);
lean_ctor_set(v_msgData_574_, 1, v___x_573_);
v___x_575_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(v_msgData_574_, v_macroStack_554_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_580_, lean_object* v_macroStack_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_580_, v_macroStack_581_, v___y_582_);
lean_dec_ref(v___y_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_ref_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v_macroStack_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_ref_593_ = lean_ctor_get(v___y_590_, 5);
v___x_594_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_585_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref(v___x_594_);
v_macroStack_596_ = lean_ctor_get(v___y_586_, 1);
lean_inc(v_macroStack_596_);
lean_dec_ref(v___y_586_);
lean_inc(v_macroStack_596_);
v___x_597_ = l_Lean_Elab_getBetterRef(v_ref_593_, v_macroStack_596_);
v___x_598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_595_, v_macroStack_596_, v___y_590_);
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_597_);
lean_ctor_set(v___x_603_, 1, v_a_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 1);
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
return v_res_616_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Array_mkArray0(lean_box(0));
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_664_ = l_String_toRawSubstring_x27(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_711_, lean_object* v_decl_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
if (lean_obj_tag(v_letOrReassign_711_) == 2)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_712_);
v___x_721_ = l_Lean_Syntax_isOfKind(v_decl_712_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_723_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_724_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Lean_Syntax_getArg(v_decl_712_, v___x_726_);
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_727_);
v___x_729_ = l_Lean_Syntax_isOfKind(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___y_732_; lean_object* v_pattern_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; uint8_t v___x_802_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_727_);
v___x_802_ = l_Lean_Syntax_isOfKind(v___x_727_, v___x_730_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___x_727_);
v___x_803_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_804_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_805_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = l_Lean_Syntax_getArg(v___x_727_, v___x_807_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_808_, v___x_726_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v___x_727_);
v___x_810_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_811_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_812_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_813_;
}
else
{
lean_object* v_pattern_814_; lean_object* v_xType_x3f_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_pattern_814_ = l_Lean_Syntax_getArg(v___x_727_, v___x_726_);
v___x_849_ = lean_unsigned_to_nat(2u);
v___x_850_ = l_Lean_Syntax_getArg(v___x_727_, v___x_849_);
v___x_851_ = l_Lean_Syntax_isNone(v___x_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; 
lean_inc(v___x_850_);
v___x_852_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_807_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___x_850_);
lean_dec(v_pattern_814_);
lean_dec(v___x_727_);
v___x_853_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_854_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_855_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = l_Lean_Syntax_getArg(v___x_850_, v___x_726_);
lean_dec(v___x_850_);
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_857_);
v___x_859_ = l_Lean_Syntax_isOfKind(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___x_857_);
lean_dec(v_pattern_814_);
lean_dec(v___x_727_);
v___x_860_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_861_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_862_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_863_;
}
else
{
lean_object* v_xType_x3f_864_; lean_object* v___x_865_; 
lean_dec(v_decl_712_);
v_xType_x3f_864_ = l_Lean_Syntax_getArg(v___x_857_, v___x_807_);
lean_dec(v___x_857_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_xType_x3f_864_);
v_xType_x3f_816_ = v___x_865_;
v___y_817_ = v_a_713_;
v___y_818_ = v_a_714_;
v___y_819_ = v_a_715_;
v___y_820_ = v_a_716_;
v___y_821_ = v_a_717_;
v___y_822_ = v_a_718_;
goto v___jp_815_;
}
}
}
else
{
lean_object* v___x_866_; 
lean_dec(v___x_850_);
lean_dec(v_decl_712_);
v___x_866_ = lean_box(0);
v_xType_x3f_816_ = v___x_866_;
v___y_817_ = v_a_713_;
v___y_818_ = v_a_714_;
v___y_819_ = v_a_715_;
v___y_820_ = v_a_716_;
v___y_821_ = v_a_717_;
v___y_822_ = v_a_718_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(4u);
v___x_824_ = l_Lean_Syntax_getArg(v___x_727_, v___x_823_);
lean_dec(v___x_727_);
if (lean_obj_tag(v_xType_x3f_816_) == 0)
{
v___y_732_ = v___x_824_;
v_pattern_733_ = v_pattern_814_;
v___y_734_ = v___y_817_;
v___y_735_ = v___y_818_;
v___y_736_ = v___y_819_;
v___y_737_ = v___y_820_;
v___y_738_ = v___y_821_;
v___y_739_ = v___y_822_;
goto v___jp_731_;
}
else
{
lean_object* v_val_825_; lean_object* v_ref_826_; lean_object* v_quotContext_827_; lean_object* v_currMacroScope_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_val_825_ = lean_ctor_get(v_xType_x3f_816_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v_xType_x3f_816_);
v_ref_826_ = lean_ctor_get(v___y_821_, 5);
v_quotContext_827_ = lean_ctor_get(v___y_821_, 10);
v_currMacroScope_828_ = lean_ctor_get(v___y_821_, 11);
v___x_829_ = l_Lean_SourceInfo_fromRef(v_ref_826_, v___x_729_);
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_829_);
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_829_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_835_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_836_ = lean_box(0);
lean_inc(v_currMacroScope_828_);
lean_inc(v_quotContext_827_);
v___x_837_ = l_Lean_addMacroScope(v_quotContext_827_, v___x_836_, v_currMacroScope_828_);
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
lean_inc(v___x_829_);
v___x_839_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_839_, 0, v___x_829_);
lean_ctor_set(v___x_839_, 1, v___x_835_);
lean_ctor_set(v___x_839_, 2, v___x_837_);
lean_ctor_set(v___x_839_, 3, v___x_838_);
lean_inc(v___x_829_);
v___x_840_ = l_Lean_Syntax_node1(v___x_829_, v___x_834_, v___x_839_);
lean_inc(v___x_829_);
v___x_841_ = l_Lean_Syntax_node2(v___x_829_, v___x_831_, v___x_833_, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_829_);
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_829_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
lean_inc(v___x_829_);
v___x_845_ = l_Lean_Syntax_node1(v___x_829_, v___x_844_, v_val_825_);
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_829_);
v___x_847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_829_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_Syntax_node5(v___x_829_, v___x_830_, v___x_841_, v_pattern_814_, v___x_843_, v___x_845_, v___x_847_);
v___y_732_ = v___x_824_;
v_pattern_733_ = v___x_848_;
v___y_734_ = v___y_817_;
v___y_735_ = v___y_818_;
v___y_736_ = v___y_819_;
v___y_737_ = v___y_820_;
v___y_738_ = v___y_821_;
v___y_739_ = v___y_822_;
goto v___jp_731_;
}
}
}
}
v___jp_731_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_740_ = lean_box(0);
v___x_741_ = lean_box(v___x_721_);
v___x_742_ = lean_box(v___x_721_);
lean_inc(v_pattern_733_);
v___x_743_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_743_, 0, v_pattern_733_);
lean_closure_set(v___x_743_, 1, v___x_740_);
lean_closure_set(v___x_743_, 2, v___x_741_);
lean_closure_set(v___x_743_, 3, v___x_742_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
v___x_744_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_743_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
v___x_746_ = lean_infer_type(v_a_745_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
lean_inc_ref(v___y_738_);
v___x_748_ = l_Lean_Elab_Term_exprToSyntax(v_a_747_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_785_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_785_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_785_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_785_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_ref_753_; lean_object* v_quotContext_754_; lean_object* v_currMacroScope_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v_ref_753_ = lean_ctor_get(v___y_738_, 5);
lean_inc(v_ref_753_);
v_quotContext_754_ = lean_ctor_get(v___y_738_, 10);
lean_inc(v_quotContext_754_);
v_currMacroScope_755_ = lean_ctor_get(v___y_738_, 11);
lean_inc(v_currMacroScope_755_);
lean_dec_ref(v___y_738_);
v___x_756_ = l_Lean_SourceInfo_fromRef(v_ref_753_, v___x_729_);
lean_dec(v_ref_753_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_758_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_756_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_756_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_756_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_756_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_756_);
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_756_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_767_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_768_ = lean_box(0);
v___x_769_ = l_Lean_addMacroScope(v_quotContext_754_, v___x_768_, v_currMacroScope_755_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
lean_inc(v___x_756_);
v___x_771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_771_, 0, v___x_756_);
lean_ctor_set(v___x_771_, 1, v___x_767_);
lean_ctor_set(v___x_771_, 2, v___x_769_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
lean_inc(v___x_756_);
v___x_772_ = l_Lean_Syntax_node1(v___x_756_, v___x_766_, v___x_771_);
lean_inc(v___x_756_);
v___x_773_ = l_Lean_Syntax_node2(v___x_756_, v___x_763_, v___x_765_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_756_);
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_756_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
lean_inc(v___x_756_);
v___x_776_ = l_Lean_Syntax_node1(v___x_756_, v___x_757_, v_a_749_);
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_756_);
v___x_778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_756_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
lean_inc(v___x_756_);
v___x_779_ = l_Lean_Syntax_node5(v___x_756_, v___x_762_, v___x_773_, v___y_732_, v___x_775_, v___x_776_, v___x_778_);
lean_inc_ref(v___x_759_);
lean_inc(v___x_756_);
v___x_780_ = l_Lean_Syntax_node5(v___x_756_, v___x_730_, v_pattern_733_, v___x_759_, v___x_759_, v___x_761_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node1(v___x_756_, v___x_720_, v___x_780_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_781_);
v___x_783_ = v___x_751_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_dec_ref(v___y_738_);
lean_dec(v_pattern_733_);
lean_dec(v___y_732_);
return v___x_748_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v_pattern_733_);
lean_dec(v___y_732_);
v_a_786_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_746_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_746_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v_pattern_733_);
lean_dec(v___y_732_);
v_a_794_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_744_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_744_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_867_ = l_Lean_Syntax_getArg(v___x_727_, v___x_726_);
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_867_);
v___x_869_ = l_Lean_Syntax_isOfKind(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v___x_867_);
lean_dec(v___x_727_);
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_871_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_872_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_873_;
}
else
{
lean_object* v_x_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v_a_883_; lean_object* v_xType_x3f_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_x_874_ = l_Lean_Syntax_getArg(v___x_867_, v___x_726_);
lean_dec(v___x_867_);
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_874_);
v___x_961_ = l_Lean_Syntax_isOfKind(v_x_874_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_x_874_);
lean_dec(v___x_727_);
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_963_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_964_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = l_Lean_Syntax_getArg(v___x_727_, v___x_966_);
v___x_968_ = l_Lean_Syntax_matchesNull(v___x_967_, v___x_726_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_x_874_);
lean_dec(v___x_727_);
v___x_969_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_970_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_971_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_unsigned_to_nat(2u);
v___x_974_ = l_Lean_Syntax_getArg(v___x_727_, v___x_973_);
v___x_975_ = l_Lean_Syntax_isNone(v___x_974_);
if (v___x_975_ == 0)
{
uint8_t v___x_976_; 
lean_inc(v___x_974_);
v___x_976_ = l_Lean_Syntax_matchesNull(v___x_974_, v___x_966_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v___x_974_);
lean_dec(v_x_874_);
lean_dec(v___x_727_);
v___x_977_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_978_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_979_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = l_Lean_Syntax_getArg(v___x_974_, v___x_726_);
lean_dec(v___x_974_);
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_981_);
v___x_983_ = l_Lean_Syntax_isOfKind(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v___x_981_);
lean_dec(v_x_874_);
lean_dec(v___x_727_);
v___x_984_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_985_ = l_Lean_MessageData_ofSyntax(v_decl_712_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_986_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v___x_987_;
}
else
{
lean_object* v_xType_x3f_988_; lean_object* v___x_989_; 
lean_dec(v_decl_712_);
v_xType_x3f_988_ = l_Lean_Syntax_getArg(v___x_981_, v___x_966_);
lean_dec(v___x_981_);
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v_xType_x3f_988_);
v_xType_x3f_932_ = v___x_989_;
v___y_933_ = v_a_713_;
v___y_934_ = v_a_714_;
v___y_935_ = v_a_715_;
v___y_936_ = v_a_716_;
v___y_937_ = v_a_717_;
v___y_938_ = v_a_718_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v___x_990_; 
lean_dec(v___x_974_);
lean_dec(v_decl_712_);
v___x_990_ = lean_box(0);
v_xType_x3f_932_ = v___x_990_;
v___y_933_ = v_a_713_;
v___y_934_ = v_a_714_;
v___y_935_ = v_a_715_;
v___y_936_ = v_a_716_;
v___y_937_ = v_a_717_;
v___y_938_ = v_a_718_;
goto v___jp_931_;
}
}
}
v___jp_875_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_box(0);
lean_inc(v___y_878_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_880_);
lean_inc(v_x_874_);
v___x_885_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_874_, v_a_883_, v___x_721_, v___x_721_, v___x_884_, v___y_880_, v___y_879_, v___y_877_, v___y_881_, v___y_876_, v___y_878_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v___x_885_);
v___x_886_ = l_Lean_TSyntax_getId(v_x_874_);
v___x_887_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_886_, v___y_877_, v___y_881_, v___y_876_, v___y_878_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_LocalDecl_type(v_a_888_);
lean_dec(v_a_888_);
lean_inc_ref(v___y_876_);
v___x_890_ = l_Lean_Elab_Term_exprToSyntax(v___x_889_, v___y_880_, v___y_879_, v___y_877_, v___y_881_, v___y_876_, v___y_878_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_914_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_914_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_914_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_914_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_ref_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_ref_895_ = lean_ctor_get(v___y_876_, 5);
lean_inc(v_ref_895_);
lean_dec_ref(v___y_876_);
v___x_896_ = 0;
v___x_897_ = l_Lean_SourceInfo_fromRef(v_ref_895_, v___x_896_);
lean_dec(v_ref_895_);
lean_inc(v___x_897_);
v___x_898_ = l_Lean_Syntax_node1(v___x_897_, v___x_868_, v_x_874_);
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_900_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_897_);
v___x_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_901_, 0, v___x_897_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_897_);
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_897_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
lean_inc(v___x_897_);
v___x_905_ = l_Lean_Syntax_node2(v___x_897_, v___x_902_, v___x_904_, v_a_891_);
lean_inc(v___x_897_);
v___x_906_ = l_Lean_Syntax_node1(v___x_897_, v___x_899_, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_897_);
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_897_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
lean_inc(v___x_897_);
v___x_909_ = l_Lean_Syntax_node5(v___x_897_, v___x_728_, v___x_898_, v___x_901_, v___x_906_, v___x_908_, v___y_882_);
v___x_910_ = l_Lean_Syntax_node1(v___x_897_, v___x_720_, v___x_909_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_910_);
v___x_912_ = v___x_893_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_dec(v___y_882_);
lean_dec_ref(v___y_876_);
lean_dec(v_x_874_);
return v___x_890_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_x_874_);
v_a_915_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_887_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_887_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_x_874_);
v_a_923_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_885_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_885_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
v___jp_931_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(4u);
v___x_940_ = l_Lean_Syntax_getArg(v___x_727_, v___x_939_);
lean_dec(v___x_727_);
if (lean_obj_tag(v_xType_x3f_932_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
v___y_876_ = v___y_937_;
v___y_877_ = v___y_935_;
v___y_878_ = v___y_938_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_933_;
v___y_881_ = v___y_936_;
v___y_882_ = v___x_940_;
v_a_883_ = v___x_941_;
goto v___jp_875_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_959_; 
v_val_942_ = lean_ctor_get(v_xType_x3f_932_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_xType_x3f_932_);
if (v_isSharedCheck_959_ == 0)
{
v___x_944_ = v_xType_x3f_932_;
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_xType_x3f_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
v___x_946_ = l_Lean_Elab_Term_elabType(v_val_942_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_a_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
v___y_876_ = v___y_937_;
v___y_877_ = v___y_935_;
v___y_878_ = v___y_938_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_933_;
v___y_881_ = v___y_936_;
v___y_882_ = v___x_940_;
v_a_883_ = v___x_949_;
goto v___jp_875_;
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_944_);
lean_dec(v___x_940_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_x_874_);
v_a_951_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_946_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_946_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
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
lean_object* v___x_991_; 
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_decl_712_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_992_, lean_object* v_decl_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_992_, v_decl_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_letOrReassign_992_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_1012_, v_msg_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_1022_, lean_object* v_macroStack_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_1022_, v_macroStack_1023_, v___y_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_1032_, lean_object* v_macroStack_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_1032_, v_macroStack_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1041_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_keyedConfig_1079_; uint8_t v_trackZetaDelta_1080_; lean_object* v_zetaDeltaSet_1081_; lean_object* v_localInstances_1082_; lean_object* v_defEqCtx_x3f_1083_; lean_object* v_synthPendingDepth_1084_; lean_object* v_canUnfold_x3f_1085_; uint8_t v_univApprox_1086_; uint8_t v_inTypeClassResolution_1087_; uint8_t v_cacheInferType_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1104_; 
v_keyedConfig_1079_ = lean_ctor_get(v___y_1074_, 0);
v_trackZetaDelta_1080_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*7);
v_zetaDeltaSet_1081_ = lean_ctor_get(v___y_1074_, 1);
v_localInstances_1082_ = lean_ctor_get(v___y_1074_, 3);
v_defEqCtx_x3f_1083_ = lean_ctor_get(v___y_1074_, 4);
v_synthPendingDepth_1084_ = lean_ctor_get(v___y_1074_, 5);
v_canUnfold_x3f_1085_ = lean_ctor_get(v___y_1074_, 6);
v_univApprox_1086_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1087_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*7 + 2);
v_cacheInferType_1088_ = lean_ctor_get_uint8(v___y_1074_, sizeof(void*)*7 + 3);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___y_1074_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v___y_1074_, 2);
lean_dec(v_unused_1105_);
v___x_1090_ = v___y_1074_;
v_isShared_1091_ = v_isSharedCheck_1104_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_canUnfold_x3f_1085_);
lean_inc(v_synthPendingDepth_1084_);
lean_inc(v_defEqCtx_x3f_1083_);
lean_inc(v_localInstances_1082_);
lean_inc(v_zetaDeltaSet_1081_);
lean_inc(v_keyedConfig_1079_);
lean_dec(v___y_1074_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1104_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 2, v_lctx_1070_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_keyedConfig_1079_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_zetaDeltaSet_1081_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_lctx_1070_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_localInstances_1082_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_defEqCtx_x3f_1083_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_synthPendingDepth_1084_);
lean_ctor_set(v_reuseFailAlloc_1103_, 6, v_canUnfold_x3f_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*7, v_trackZetaDelta_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*7 + 1, v_univApprox_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*7 + 3, v_cacheInferType_1088_);
v___x_1093_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_apply_7(v_x_1071_, v___y_1072_, v___y_1073_, v___x_1093_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1106_, v_x_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1116_, lean_object* v_lctx_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1117_, v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_lctx_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1127_, v_lctx_1128_, v_x_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_options_1144_; uint8_t v_hasTrace_1145_; 
v_options_1144_ = lean_ctor_get(v___y_1142_, 2);
v_hasTrace_1145_ = lean_ctor_get_uint8(v_options_1144_, sizeof(void*)*1);
if (v_hasTrace_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v_cls_1141_);
v___x_1146_ = lean_box(v_hasTrace_1145_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v_inheritedTraceOptions_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_inheritedTraceOptions_1148_ = lean_ctor_get(v___y_1142_, 13);
v___x_1149_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_1150_ = l_Lean_Name_append(v___x_1149_, v_cls_1141_);
v___x_1151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1148_, v_options_1144_, v___x_1150_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_box(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_cls_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_1154_, v___y_1155_);
lean_dec_ref(v___y_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_1158_, v___y_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0(lean_object* v_k_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_apply_9(v_k_1178_, v_b_1182_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0___boxed(lean_object* v_k_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0(v_k_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_name_1200_, lean_object* v_type_1201_, lean_object* v_val_1202_, lean_object* v_k_1203_, uint8_t v_nondep_1204_, uint8_t v_kind_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___f_1214_; lean_object* v___x_1215_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1214_, 0, v_k_1203_);
lean_closure_set(v___f_1214_, 1, v___y_1206_);
lean_closure_set(v___f_1214_, 2, v___y_1207_);
lean_closure_set(v___f_1214_, 3, v___y_1208_);
v___x_1215_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1200_, v_type_1201_, v_val_1202_, v___f_1214_, v_nondep_1204_, v_kind_1205_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1215_) == 0)
{
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_name_1224_, lean_object* v_type_1225_, lean_object* v_val_1226_, lean_object* v_k_1227_, lean_object* v_nondep_1228_, lean_object* v_kind_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v_nondep_boxed_1238_; uint8_t v_kind_boxed_1239_; lean_object* v_res_1240_; 
v_nondep_boxed_1238_ = lean_unbox(v_nondep_1228_);
v_kind_boxed_1239_ = lean_unbox(v_kind_1229_);
v_res_1240_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_name_1224_, v_type_1225_, v_val_1226_, v_k_1227_, v_nondep_boxed_1238_, v_kind_boxed_1239_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_00_u03b1_1241_, lean_object* v_name_1242_, lean_object* v_type_1243_, lean_object* v_val_1244_, lean_object* v_k_1245_, uint8_t v_nondep_1246_, uint8_t v_kind_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_name_1242_, v_type_1243_, v_val_1244_, v_k_1245_, v_nondep_1246_, v_kind_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_name_1258_, lean_object* v_type_1259_, lean_object* v_val_1260_, lean_object* v_k_1261_, lean_object* v_nondep_1262_, lean_object* v_kind_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v_nondep_boxed_1272_; uint8_t v_kind_boxed_1273_; lean_object* v_res_1274_; 
v_nondep_boxed_1272_ = lean_unbox(v_nondep_1262_);
v_kind_boxed_1273_ = lean_unbox(v_kind_1263_);
v_res_1274_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_00_u03b1_1257_, v_name_1258_, v_type_1259_, v_val_1260_, v_k_1261_, v_nondep_boxed_1272_, v_kind_boxed_1273_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1275_, lean_object* v___x_1276_, uint8_t v___x_1277_, lean_object* v___x_1278_, lean_object* v___x_1279_, uint8_t v___x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
v___x_1288_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1275_, v___x_1276_, v___x_1277_, v___x_1277_, v___x_1278_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = 1;
v___x_1291_ = l_Lean_Meta_mkLambdaFVars(v___x_1279_, v_a_1289_, v___x_1280_, v___x_1280_, v___x_1280_, v___x_1277_, v___x_1290_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v___x_1291_;
}
else
{
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v___x_75016__boxed_1305_; uint8_t v___x_75019__boxed_1306_; lean_object* v_res_1307_; 
v___x_75016__boxed_1305_ = lean_unbox(v___x_1294_);
v___x_75019__boxed_1306_ = lean_unbox(v___x_1297_);
v_res_1307_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1292_, v___x_1293_, v___x_75016__boxed_1305_, v___x_1295_, v___x_1296_, v___x_75019__boxed_1306_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec_ref(v___x_1296_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v_ks_1312_; lean_object* v_vs_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1337_; 
v_ks_1312_ = lean_ctor_get(v_x_1308_, 0);
v_vs_1313_ = lean_ctor_get(v_x_1308_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1308_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1315_ = v_x_1308_;
v_isShared_1316_ = v_isSharedCheck_1337_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_vs_1313_);
lean_inc(v_ks_1312_);
lean_dec(v_x_1308_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1337_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_get_size(v_ks_1312_);
v___x_1318_ = lean_nat_dec_lt(v_x_1309_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_x_1309_);
v___x_1319_ = lean_array_push(v_ks_1312_, v_x_1310_);
v___x_1320_ = lean_array_push(v_vs_1313_, v_x_1311_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1320_);
lean_ctor_set(v___x_1315_, 0, v___x_1319_);
v___x_1322_ = v___x_1315_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v_k_x27_1324_; uint8_t v___x_1325_; 
v_k_x27_1324_ = lean_array_fget_borrowed(v_ks_1312_, v_x_1309_);
v___x_1325_ = l_Lean_instBEqFVarId_beq(v_x_1310_, v_k_x27_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1327_; 
if (v_isShared_1316_ == 0)
{
v___x_1327_ = v___x_1315_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_ks_1312_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_vs_1313_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_x_1309_, v___x_1328_);
lean_dec(v_x_1309_);
v_x_1308_ = v___x_1327_;
v_x_1309_ = v___x_1329_;
goto _start;
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = lean_array_fset(v_ks_1312_, v_x_1309_, v_x_1310_);
v___x_1333_ = lean_array_fset(v_vs_1313_, v_x_1309_, v_x_1311_);
lean_dec(v_x_1309_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1333_);
lean_ctor_set(v___x_1315_, 0, v___x_1332_);
v___x_1335_ = v___x_1315_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(lean_object* v_n_1338_, lean_object* v_k_1339_, lean_object* v_v_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(v_n_1338_, v___x_1341_, v_k_1339_, v_v_1340_);
return v___x_1342_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; 
v___x_1343_ = ((size_t)5ULL);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_shift_left(v___x_1344_, v___x_1343_);
return v___x_1345_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; 
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1348_ = lean_usize_sub(v___x_1347_, v___x_1346_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1350_, size_t v_x_1351_, size_t v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
if (lean_obj_tag(v_x_1350_) == 0)
{
lean_object* v_es_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v_j_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_es_1355_ = lean_ctor_get(v_x_1350_, 0);
v___x_1356_ = ((size_t)5ULL);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_1359_ = lean_usize_land(v_x_1351_, v___x_1358_);
v_j_1360_ = lean_usize_to_nat(v___x_1359_);
v___x_1361_ = lean_array_get_size(v_es_1355_);
v___x_1362_ = lean_nat_dec_lt(v_j_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v_j_1360_);
lean_dec(v_x_1354_);
lean_dec(v_x_1353_);
return v_x_1350_;
}
else
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1399_; 
lean_inc_ref(v_es_1355_);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_x_1350_, 0);
lean_dec(v_unused_1400_);
v___x_1364_ = v_x_1350_;
v_isShared_1365_ = v_isSharedCheck_1399_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_x_1350_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1399_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_v_1366_; lean_object* v___x_1367_; lean_object* v_xs_x27_1368_; lean_object* v___y_1370_; 
v_v_1366_ = lean_array_fget(v_es_1355_, v_j_1360_);
v___x_1367_ = lean_box(0);
v_xs_x27_1368_ = lean_array_fset(v_es_1355_, v_j_1360_, v___x_1367_);
switch(lean_obj_tag(v_v_1366_))
{
case 0:
{
lean_object* v_key_1375_; lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1386_; 
v_key_1375_ = lean_ctor_get(v_v_1366_, 0);
v_val_1376_ = lean_ctor_get(v_v_1366_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1378_ = v_v_1366_;
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_inc(v_key_1375_);
lean_dec(v_v_1366_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_instBEqFVarId_beq(v_x_1353_, v_key_1375_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1378_);
v___x_1381_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1375_, v_val_1376_, v_x_1353_, v_x_1354_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___y_1370_ = v___x_1382_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_val_1376_);
lean_dec(v_key_1375_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v_x_1354_);
lean_ctor_set(v___x_1378_, 0, v_x_1353_);
v___x_1384_ = v___x_1378_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_x_1353_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_x_1354_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
v___y_1370_ = v___x_1384_;
goto v___jp_1369_;
}
}
}
}
case 1:
{
lean_object* v_node_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_node_1387_ = lean_ctor_get(v_v_1366_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1389_ = v_v_1366_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_node_1387_);
lean_dec(v_v_1366_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1391_ = lean_usize_shift_right(v_x_1351_, v___x_1356_);
v___x_1392_ = lean_usize_add(v_x_1352_, v___x_1357_);
v___x_1393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1387_, v___x_1391_, v___x_1392_, v_x_1353_, v_x_1354_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
v___y_1370_ = v___x_1395_;
goto v___jp_1369_;
}
}
}
default: 
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_x_1353_);
lean_ctor_set(v___x_1398_, 1, v_x_1354_);
v___y_1370_ = v___x_1398_;
goto v___jp_1369_;
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_array_fset(v_xs_x27_1368_, v_j_1360_, v___y_1370_);
lean_dec(v_j_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1371_);
v___x_1373_ = v___x_1364_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v_ks_1401_; lean_object* v_vs_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1422_; 
v_ks_1401_ = lean_ctor_get(v_x_1350_, 0);
v_vs_1402_ = lean_ctor_get(v_x_1350_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1404_ = v_x_1350_;
v_isShared_1405_ = v_isSharedCheck_1422_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_vs_1402_);
lean_inc(v_ks_1401_);
lean_dec(v_x_1350_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1422_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_ks_1401_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_vs_1402_);
v___x_1407_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v_newNode_1408_; uint8_t v___y_1410_; size_t v___x_1416_; uint8_t v___x_1417_; 
v_newNode_1408_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v___x_1407_, v_x_1353_, v_x_1354_);
v___x_1416_ = ((size_t)7ULL);
v___x_1417_ = lean_usize_dec_le(v___x_1416_, v_x_1352_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1408_);
v___x_1419_ = lean_unsigned_to_nat(4u);
v___x_1420_ = lean_nat_dec_lt(v___x_1418_, v___x_1419_);
lean_dec(v___x_1418_);
v___y_1410_ = v___x_1420_;
goto v___jp_1409_;
}
else
{
v___y_1410_ = v___x_1417_;
goto v___jp_1409_;
}
v___jp_1409_:
{
if (v___y_1410_ == 0)
{
lean_object* v_ks_1411_; lean_object* v_vs_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_ks_1411_ = lean_ctor_get(v_newNode_1408_, 0);
lean_inc_ref(v_ks_1411_);
v_vs_1412_ = lean_ctor_get(v_newNode_1408_, 1);
lean_inc_ref(v_vs_1412_);
lean_dec_ref(v_newNode_1408_);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2);
v___x_1415_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_x_1352_, v_ks_1411_, v_vs_1412_, v___x_1413_, v___x_1414_);
lean_dec_ref(v_vs_1412_);
lean_dec_ref(v_ks_1411_);
return v___x_1415_;
}
else
{
return v_newNode_1408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(size_t v_depth_1423_, lean_object* v_keys_1424_, lean_object* v_vals_1425_, lean_object* v_i_1426_, lean_object* v_entries_1427_){
_start:
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_array_get_size(v_keys_1424_);
v___x_1429_ = lean_nat_dec_lt(v_i_1426_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_dec(v_i_1426_);
return v_entries_1427_;
}
else
{
lean_object* v_k_1430_; lean_object* v_v_1431_; uint64_t v___x_1432_; size_t v_h_1433_; size_t v___x_1434_; lean_object* v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; size_t v_h_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_k_1430_ = lean_array_fget_borrowed(v_keys_1424_, v_i_1426_);
v_v_1431_ = lean_array_fget_borrowed(v_vals_1425_, v_i_1426_);
v___x_1432_ = l_Lean_instHashableFVarId_hash(v_k_1430_);
v_h_1433_ = lean_uint64_to_usize(v___x_1432_);
v___x_1434_ = ((size_t)5ULL);
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_sub(v_depth_1423_, v___x_1436_);
v___x_1438_ = lean_usize_mul(v___x_1434_, v___x_1437_);
v_h_1439_ = lean_usize_shift_right(v_h_1433_, v___x_1438_);
v___x_1440_ = lean_nat_add(v_i_1426_, v___x_1435_);
lean_dec(v_i_1426_);
lean_inc(v_v_1431_);
lean_inc(v_k_1430_);
v___x_1441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1427_, v_h_1439_, v_depth_1423_, v_k_1430_, v_v_1431_);
v_i_1426_ = v___x_1440_;
v_entries_1427_ = v___x_1441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_depth_1443_, lean_object* v_keys_1444_, lean_object* v_vals_1445_, lean_object* v_i_1446_, lean_object* v_entries_1447_){
_start:
{
size_t v_depth_boxed_1448_; lean_object* v_res_1449_; 
v_depth_boxed_1448_ = lean_unbox_usize(v_depth_1443_);
lean_dec(v_depth_1443_);
v_res_1449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_depth_boxed_1448_, v_keys_1444_, v_vals_1445_, v_i_1446_, v_entries_1447_);
lean_dec_ref(v_vals_1445_);
lean_dec_ref(v_keys_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_){
_start:
{
size_t v_x_75151__boxed_1455_; size_t v_x_75152__boxed_1456_; lean_object* v_res_1457_; 
v_x_75151__boxed_1455_ = lean_unbox_usize(v_x_1451_);
lean_dec(v_x_1451_);
v_x_75152__boxed_1456_ = lean_unbox_usize(v_x_1452_);
lean_dec(v_x_1452_);
v_res_1457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1450_, v_x_75151__boxed_1455_, v_x_75152__boxed_1456_, v_x_1453_, v_x_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
uint64_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = l_Lean_instHashableFVarId_hash(v_x_1459_);
v___x_1462_ = lean_uint64_to_usize(v___x_1461_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1458_, v___x_1462_, v___x_1463_, v_x_1459_, v_x_1460_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1465_, size_t v_i_1466_, size_t v_stop_1467_, lean_object* v_b_1468_){
_start:
{
lean_object* v___y_1470_; uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_eq(v_i_1466_, v_stop_1467_);
if (v___x_1474_ == 0)
{
lean_object* v_fvarIdToDecl_1475_; lean_object* v_decls_1476_; lean_object* v_auxDeclToFullName_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_fvarIdToDecl_1475_ = lean_ctor_get(v_b_1468_, 0);
v_decls_1476_ = lean_ctor_get(v_b_1468_, 1);
v_auxDeclToFullName_1477_ = lean_ctor_get(v_b_1468_, 2);
v___x_1478_ = lean_array_uget_borrowed(v_as_1465_, v_i_1466_);
v___x_1479_ = l_Lean_Expr_fvarId_x21(v___x_1478_);
lean_inc_ref(v_b_1468_);
v___x_1480_ = lean_local_ctx_find(v_b_1468_, v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
v___y_1470_ = v_b_1468_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1507_; 
lean_inc(v_auxDeclToFullName_1477_);
lean_inc_ref(v_decls_1476_);
lean_inc_ref(v_fvarIdToDecl_1475_);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_b_1468_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1508_ = lean_ctor_get(v_b_1468_, 2);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_b_1468_, 1);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_b_1468_, 0);
lean_dec(v_unused_1510_);
v___x_1482_ = v_b_1468_;
v_isShared_1483_ = v_isSharedCheck_1507_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v_b_1468_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1507_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_val_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1506_; 
v_val_1484_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1486_ = v___x_1480_;
v_isShared_1487_ = v_isSharedCheck_1506_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_val_1484_);
lean_dec(v___x_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1506_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1502_; lean_object* v_fvarId_1505_; 
v___x_1488_ = l_Lean_LocalDecl_type(v_val_1484_);
v___x_1489_ = l_Lean_Expr_cleanupAnnotations(v___x_1488_);
v___x_1490_ = l_Lean_LocalDecl_setType(v_val_1484_, v___x_1489_);
v_fvarId_1505_ = lean_ctor_get(v___x_1490_, 1);
lean_inc(v_fvarId_1505_);
v___y_1502_ = v_fvarId_1505_;
goto v___jp_1501_;
v___jp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1495_ = v___x_1486_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1490_);
v___x_1495_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = l_Lean_PersistentArray_set___redArg(v_decls_1476_, v___y_1493_, v___x_1495_);
lean_dec(v___y_1493_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1496_);
lean_ctor_set(v___x_1482_, 0, v___y_1492_);
v___x_1498_ = v___x_1482_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___y_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_auxDeclToFullName_1477_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v___y_1470_ = v___x_1498_;
goto v___jp_1469_;
}
}
}
v___jp_1501_:
{
lean_object* v___x_1503_; lean_object* v_index_1504_; 
lean_inc_ref(v___x_1490_);
v___x_1503_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1475_, v___y_1502_, v___x_1490_);
v_index_1504_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_index_1504_);
v___y_1492_ = v___x_1503_;
v___y_1493_ = v_index_1504_;
goto v___jp_1491_;
}
}
}
}
}
else
{
return v_b_1468_;
}
v___jp_1469_:
{
size_t v___x_1471_; size_t v___x_1472_; 
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_add(v_i_1466_, v___x_1471_);
v_i_1466_ = v___x_1472_;
v_b_1468_ = v___y_1470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1511_, lean_object* v_i_1512_, lean_object* v_stop_1513_, lean_object* v_b_1514_){
_start:
{
size_t v_i_boxed_1515_; size_t v_stop_boxed_1516_; lean_object* v_res_1517_; 
v_i_boxed_1515_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_stop_boxed_1516_ = lean_unbox_usize(v_stop_1513_);
lean_dec(v_stop_1513_);
v_res_1517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1511_, v_i_boxed_1515_, v_stop_boxed_1516_, v_b_1514_);
lean_dec_ref(v_as_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_bs_1520_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1521_ == 0)
{
return v_bs_1520_;
}
else
{
lean_object* v_v_1522_; lean_object* v_snd_1523_; lean_object* v___x_1524_; lean_object* v_bs_x27_1525_; size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v_v_1522_ = lean_array_uget_borrowed(v_bs_1520_, v_i_1519_);
v_snd_1523_ = lean_ctor_get(v_v_1522_, 1);
lean_inc(v_snd_1523_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v_bs_x27_1525_ = lean_array_uset(v_bs_1520_, v_i_1519_, v___x_1524_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1519_, v___x_1526_);
v___x_1528_ = lean_array_uset(v_bs_x27_1525_, v_i_1519_, v_snd_1523_);
v_i_1519_ = v___x_1527_;
v_bs_1520_ = v___x_1528_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_bs_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1533_, v_i_boxed_1534_, v_bs_1532_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1547_, lean_object* v_value_1548_, uint8_t v___x_1549_, uint8_t v___x_1550_, lean_object* v___x_1551_, uint8_t v___y_1552_, lean_object* v_xs_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
lean_inc(v_type_1547_);
v___x_1561_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1561_, 0, v_type_1547_);
v___x_1562_ = 2;
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
v___x_1563_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1561_, v___x_1562_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; lean_object* v___y_1605_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1563_);
v_sz_1565_ = lean_array_size(v_xs_1553_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1565_, v___x_1566_, v_xs_1553_);
if (v___y_1552_ == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1605_ = v___x_1641_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1605_ = v___x_1642_;
goto v___jp_1604_;
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; 
lean_inc(v_a_1564_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1564_);
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_box(v___x_1549_);
v___x_1573_ = lean_box(v___x_1550_);
lean_inc_ref(v___x_1567_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1574_, 0, v_value_1548_);
lean_closure_set(v___f_1574_, 1, v___x_1570_);
lean_closure_set(v___f_1574_, 2, v___x_1572_);
lean_closure_set(v___f_1574_, 3, v___x_1571_);
lean_closure_set(v___f_1574_, 4, v___x_1567_);
lean_closure_set(v___f_1574_, 5, v___x_1573_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
v___x_1575_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1569_, v___f_1574_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = 1;
v___x_1578_ = l_Lean_Meta_mkForallFVars(v___x_1567_, v_a_1564_, v___x_1550_, v___x_1549_, v___x_1549_, v___x_1577_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v___x_1567_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1579_);
lean_ctor_set(v___x_1583_, 1, v_a_1576_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1576_);
v_a_1588_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1578_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1578_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___x_1567_);
lean_dec(v_a_1564_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
v_a_1596_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1575_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1575_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
v___x_1607_ = l_Lean_stringToMessageData(v___y_1605_);
lean_inc_ref(v___x_1607_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
lean_inc(v_type_1547_);
v___x_1611_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1564_, v_type_1547_, v___x_1610_, v___y_1555_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v___x_1611_);
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1609_);
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_inc(v_a_1564_);
v___x_1616_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1564_, v_type_1547_, v___x_1615_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_lctx_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
lean_dec_ref(v___x_1616_);
v_lctx_1617_ = lean_ctor_get(v___y_1556_, 2);
v___x_1618_ = lean_array_get_size(v___x_1567_);
v___x_1619_ = lean_nat_dec_lt(v___x_1551_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_inc_ref(v_lctx_1617_);
v___y_1569_ = v_lctx_1617_;
goto v___jp_1568_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_nat_dec_le(v___x_1618_, v___x_1618_);
if (v___x_1620_ == 0)
{
if (v___x_1619_ == 0)
{
lean_inc_ref(v_lctx_1617_);
v___y_1569_ = v_lctx_1617_;
goto v___jp_1568_;
}
else
{
size_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v_lctx_1617_);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1567_, v___x_1566_, v___x_1621_, v_lctx_1617_);
v___y_1569_ = v___x_1622_;
goto v___jp_1568_;
}
}
else
{
size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_usize_of_nat(v___x_1618_);
lean_inc_ref(v_lctx_1617_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1567_, v___x_1566_, v___x_1623_, v_lctx_1617_);
v___y_1569_ = v___x_1624_;
goto v___jp_1568_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___x_1567_);
lean_dec(v_a_1564_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v_value_1548_);
v_a_1625_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1616_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1616_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v___x_1607_);
lean_dec_ref(v___x_1567_);
lean_dec(v_a_1564_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v_value_1548_);
lean_dec(v_type_1547_);
v_a_1633_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1611_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1611_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec_ref(v_xs_1553_);
lean_dec(v_value_1548_);
lean_dec(v_type_1547_);
v_a_1643_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1563_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1563_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1651_, lean_object* v_value_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, lean_object* v___x_1655_, lean_object* v___y_1656_, lean_object* v_xs_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v___x_75470__boxed_1665_; uint8_t v___x_75471__boxed_1666_; uint8_t v___y_75473__boxed_1667_; lean_object* v_res_1668_; 
v___x_75470__boxed_1665_ = lean_unbox(v___x_1653_);
v___x_75471__boxed_1666_ = lean_unbox(v___x_1654_);
v___y_75473__boxed_1667_ = lean_unbox(v___y_1656_);
v_res_1668_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1651_, v_value_1652_, v___x_75470__boxed_1665_, v___x_75471__boxed_1666_, v___x_1655_, v___y_75473__boxed_1667_, v_xs_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___x_1655_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_dec_1669_, lean_object* v_x_1670_, uint8_t v___x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
v___x_1680_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_1669_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_mk_empty_array_with_capacity(v___x_1682_);
v___x_1684_ = lean_array_push(v___x_1683_, v_x_1670_);
v___x_1685_ = 1;
v___x_1686_ = l_Lean_Meta_mkLetFVars(v___x_1684_, v_a_1681_, v___x_1671_, v___x_1671_, v___x_1685_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v___x_1684_);
return v___x_1686_;
}
else
{
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v_x_1670_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object* v_dec_1687_, lean_object* v_x_1688_, lean_object* v___x_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_75695__boxed_1698_; lean_object* v_res_1699_; 
v___x_75695__boxed_1698_ = lean_unbox(v___x_1689_);
v_res_1699_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_dec_1687_, v_x_1688_, v___x_75695__boxed_1698_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_1700_, lean_object* v_dec_1701_, uint8_t v___x_1702_, lean_object* v_letOrReassign_1703_, lean_object* v_a_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc_ref(v_x_1705_);
v___x_1714_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1700_, v_x_1705_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v___x_1714_);
v___x_1715_ = lean_box(v___x_1702_);
v___f_1716_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 11, 3);
lean_closure_set(v___f_1716_, 0, v_dec_1701_);
lean_closure_set(v___f_1716_, 1, v_x_1705_);
lean_closure_set(v___f_1716_, 2, v___x_1715_);
v___x_1717_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1703_, v_a_1704_, v___f_1716_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_x_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_letOrReassign_1703_);
lean_dec_ref(v_dec_1701_);
v_a_1718_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1714_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1714_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object* v_id_1726_, lean_object* v_dec_1727_, lean_object* v___x_1728_, lean_object* v_letOrReassign_1729_, lean_object* v_a_1730_, lean_object* v_x_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_75737__boxed_1740_; lean_object* v_res_1741_; 
v___x_75737__boxed_1740_ = lean_unbox(v___x_1728_);
v_res_1741_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_1726_, v_dec_1727_, v___x_75737__boxed_1740_, v_letOrReassign_1729_, v_a_1730_, v_x_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v___x_1742_, lean_object* v___x_1743_, uint8_t v___x_1744_, lean_object* v___x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1742_, v___x_1743_, v___x_1744_, v___x_1744_, v___x_1745_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v___x_75794__boxed_1767_; lean_object* v_res_1768_; 
v___x_75794__boxed_1767_ = lean_unbox(v___x_1757_);
v_res_1768_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_1755_, v___x_1756_, v___x_75794__boxed_1767_, v___x_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1759_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_apply_8(v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, lean_box(0));
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_x_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0(lean_object* v_stx_1789_, lean_object* v_output_1790_, lean_object* v_trees_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_lctx_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_lctx_1799_ = lean_ctor_get(v___y_1794_, 2);
lean_inc_ref(v_lctx_1799_);
v___x_1800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1800_, 0, v_lctx_1799_);
lean_ctor_set(v___x_1800_, 1, v_stx_1789_);
lean_ctor_set(v___x_1800_, 2, v_output_1790_);
v___x_1801_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v_trees_1791_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_stx_1804_, lean_object* v_output_1805_, lean_object* v_trees_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0(v_stx_1804_, v_output_1805_, v_trees_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v_infoState_1818_; lean_object* v_trees_1819_; lean_object* v___x_1820_; lean_object* v_infoState_1821_; lean_object* v_env_1822_; lean_object* v_nextMacroScope_1823_; lean_object* v_ngen_1824_; lean_object* v_auxDeclNGen_1825_; lean_object* v_traceState_1826_; lean_object* v_cache_1827_; lean_object* v_messages_1828_; lean_object* v_snapshotTasks_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1852_; 
v___x_1817_ = lean_st_ref_get(v___y_1815_);
v_infoState_1818_ = lean_ctor_get(v___x_1817_, 7);
lean_inc_ref(v_infoState_1818_);
lean_dec(v___x_1817_);
v_trees_1819_ = lean_ctor_get(v_infoState_1818_, 2);
lean_inc_ref(v_trees_1819_);
lean_dec_ref(v_infoState_1818_);
v___x_1820_ = lean_st_ref_take(v___y_1815_);
v_infoState_1821_ = lean_ctor_get(v___x_1820_, 7);
v_env_1822_ = lean_ctor_get(v___x_1820_, 0);
v_nextMacroScope_1823_ = lean_ctor_get(v___x_1820_, 1);
v_ngen_1824_ = lean_ctor_get(v___x_1820_, 2);
v_auxDeclNGen_1825_ = lean_ctor_get(v___x_1820_, 3);
v_traceState_1826_ = lean_ctor_get(v___x_1820_, 4);
v_cache_1827_ = lean_ctor_get(v___x_1820_, 5);
v_messages_1828_ = lean_ctor_get(v___x_1820_, 6);
v_snapshotTasks_1829_ = lean_ctor_get(v___x_1820_, 8);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1852_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snapshotTasks_1829_);
lean_inc(v_infoState_1821_);
lean_inc(v_messages_1828_);
lean_inc(v_cache_1827_);
lean_inc(v_traceState_1826_);
lean_inc(v_auxDeclNGen_1825_);
lean_inc(v_ngen_1824_);
lean_inc(v_nextMacroScope_1823_);
lean_inc(v_env_1822_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1852_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
uint8_t v_enabled_1833_; lean_object* v_assignment_1834_; lean_object* v_lazyAssignment_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1850_; 
v_enabled_1833_ = lean_ctor_get_uint8(v_infoState_1821_, sizeof(void*)*3);
v_assignment_1834_ = lean_ctor_get(v_infoState_1821_, 0);
v_lazyAssignment_1835_ = lean_ctor_get(v_infoState_1821_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_infoState_1821_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_infoState_1821_, 2);
lean_dec(v_unused_1851_);
v___x_1837_ = v_infoState_1821_;
v_isShared_1838_ = v_isSharedCheck_1850_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_lazyAssignment_1835_);
lean_inc(v_assignment_1834_);
lean_dec(v_infoState_1821_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1850_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1839_ = lean_unsigned_to_nat(32u);
v___x_1840_ = lean_mk_empty_array_with_capacity(v___x_1839_);
lean_dec_ref(v___x_1840_);
v___x_1841_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 2, v___x_1841_);
v___x_1843_ = v___x_1837_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_assignment_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_lazyAssignment_1835_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v___x_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1849_, sizeof(void*)*3, v_enabled_1833_);
v___x_1843_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 7, v___x_1843_);
v___x_1845_ = v___x_1831_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_env_1822_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_nextMacroScope_1823_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_ngen_1824_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_auxDeclNGen_1825_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_traceState_1826_);
lean_ctor_set(v_reuseFailAlloc_1848_, 5, v_cache_1827_);
lean_ctor_set(v_reuseFailAlloc_1848_, 6, v_messages_1828_);
lean_ctor_set(v_reuseFailAlloc_1848_, 7, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1848_, 8, v_snapshotTasks_1829_);
v___x_1845_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_st_ref_set(v___y_1815_, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_trees_1819_);
return v___x_1847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg___boxed(lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_1853_);
lean_dec(v___y_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(lean_object* v___y_1856_, lean_object* v_mkInfoTree_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v_a_1863_, lean_object* v_a_x3f_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_infoState_1867_; lean_object* v_trees_1868_; lean_object* v___x_1869_; 
v___x_1866_ = lean_st_ref_get(v___y_1856_);
v_infoState_1867_ = lean_ctor_get(v___x_1866_, 7);
lean_inc_ref(v_infoState_1867_);
lean_dec(v___x_1866_);
v_trees_1868_ = lean_ctor_get(v_infoState_1867_, 2);
lean_inc_ref(v_trees_1868_);
lean_dec_ref(v_infoState_1867_);
lean_inc(v___y_1856_);
v___x_1869_ = lean_apply_8(v_mkInfoTree_1857_, v_trees_1868_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1856_, lean_box(0));
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1908_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1908_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1908_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v_infoState_1875_; lean_object* v_env_1876_; lean_object* v_nextMacroScope_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_cache_1881_; lean_object* v_messages_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1907_; 
v___x_1874_ = lean_st_ref_take(v___y_1856_);
v_infoState_1875_ = lean_ctor_get(v___x_1874_, 7);
v_env_1876_ = lean_ctor_get(v___x_1874_, 0);
v_nextMacroScope_1877_ = lean_ctor_get(v___x_1874_, 1);
v_ngen_1878_ = lean_ctor_get(v___x_1874_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1874_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1874_, 4);
v_cache_1881_ = lean_ctor_get(v___x_1874_, 5);
v_messages_1882_ = lean_ctor_get(v___x_1874_, 6);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1874_, 8);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1885_ = v___x_1874_;
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1875_);
lean_inc(v_messages_1882_);
lean_inc(v_cache_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_nextMacroScope_1877_);
lean_inc(v_env_1876_);
lean_dec(v___x_1874_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
uint8_t v_enabled_1887_; lean_object* v_assignment_1888_; lean_object* v_lazyAssignment_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1905_; 
v_enabled_1887_ = lean_ctor_get_uint8(v_infoState_1875_, sizeof(void*)*3);
v_assignment_1888_ = lean_ctor_get(v_infoState_1875_, 0);
v_lazyAssignment_1889_ = lean_ctor_get(v_infoState_1875_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_infoState_1875_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v_infoState_1875_, 2);
lean_dec(v_unused_1906_);
v___x_1891_ = v_infoState_1875_;
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_lazyAssignment_1889_);
lean_inc(v_assignment_1888_);
lean_dec(v_infoState_1875_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1905_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_PersistentArray_push___redArg(v_a_1863_, v_a_1870_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_assignment_1888_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_lazyAssignment_1889_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v___x_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1904_, sizeof(void*)*3, v_enabled_1887_);
v___x_1895_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 7, v___x_1895_);
v___x_1897_ = v___x_1885_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_env_1876_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_nextMacroScope_1877_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v_cache_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 6, v_messages_1882_);
lean_ctor_set(v_reuseFailAlloc_1903_, 7, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1903_, 8, v_snapshotTasks_1883_);
v___x_1897_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = lean_st_ref_set(v___y_1856_, v___x_1897_);
lean_dec(v___y_1856_);
v___x_1899_ = lean_box(0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1899_);
v___x_1901_ = v___x_1872_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v_a_1863_);
lean_dec(v___y_1856_);
v_a_1909_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1869_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1869_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0___boxed(lean_object* v___y_1917_, lean_object* v_mkInfoTree_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v_a_1924_, lean_object* v_a_x3f_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1917_, v_mkInfoTree_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v_a_1924_, v_a_x3f_1925_);
lean_dec(v_a_x3f_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(lean_object* v_x_1928_, lean_object* v_mkInfoTree_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_infoState_1938_; uint8_t v_enabled_1939_; 
v___x_1937_ = lean_st_ref_get(v___y_1935_);
v_infoState_1938_ = lean_ctor_get(v___x_1937_, 7);
lean_inc_ref(v_infoState_1938_);
lean_dec(v___x_1937_);
v_enabled_1939_ = lean_ctor_get_uint8(v_infoState_1938_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1938_);
if (v_enabled_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref(v_mkInfoTree_1929_);
v___x_1940_ = lean_apply_7(v_x_1928_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, lean_box(0));
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v_a_1942_; lean_object* v_r_1943_; 
v___x_1941_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_1935_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
v_r_1943_ = lean_apply_7(v_x_1928_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, lean_box(0));
if (lean_obj_tag(v_r_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1968_; 
v_a_1944_ = lean_ctor_get(v_r_1943_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_r_1943_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1946_ = v_r_1943_;
v_isShared_1947_ = v_isSharedCheck_1968_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v_r_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1968_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
lean_inc(v_a_1944_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 1);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1935_, v_mkInfoTree_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v_a_1942_, v___x_1949_);
lean_dec_ref(v___x_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v___x_1950_, 0);
lean_dec(v_unused_1958_);
v___x_1952_ = v___x_1950_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v___x_1950_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v_a_1944_);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1944_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1944_);
v_a_1959_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1950_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1950_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_a_1969_ = lean_ctor_get(v_r_1943_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v_r_1943_);
v___x_1970_ = lean_box(0);
v___x_1971_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1935_, v_mkInfoTree_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v_a_1942_, v___x_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1971_, 0);
lean_dec(v_unused_1979_);
v___x_1973_ = v___x_1971_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v___x_1971_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 1);
lean_ctor_set(v___x_1973_, 0, v_a_1969_);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1969_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1969_);
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___boxed(lean_object* v_x_1988_, lean_object* v_mkInfoTree_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_1988_, v_mkInfoTree_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(lean_object* v_stx_1998_, lean_object* v_output_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___f_2008_; lean_object* v___x_2009_; 
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2008_, 0, v_stx_1998_);
lean_closure_set(v___f_2008_, 1, v_output_1999_);
v___x_2009_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_2000_, v___f_2008_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___boxed(lean_object* v_stx_2010_, lean_object* v_output_2011_, lean_object* v_x_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_stx_2010_, v_output_2011_, v_x_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_beforeStx_2021_, lean_object* v_afterStx_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___f_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2032_, 0, v_x_2023_);
lean_closure_set(v___f_2032_, 1, v___y_2024_);
lean_inc(v_afterStx_2022_);
lean_inc(v_beforeStx_2021_);
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2033_, 0, lean_box(0));
lean_closure_set(v___x_2033_, 1, v_beforeStx_2021_);
lean_closure_set(v___x_2033_, 2, v_afterStx_2022_);
lean_closure_set(v___x_2033_, 3, v___f_2032_);
v___x_2034_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_beforeStx_2021_, v_afterStx_2022_, v___x_2033_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
if (lean_obj_tag(v___x_2034_) == 0)
{
return v___x_2034_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_beforeStx_2043_, lean_object* v_afterStx_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_beforeStx_2043_, v_afterStx_2044_, v_x_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1));
v___x_2058_ = l_String_toRawSubstring_x27(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_a_2080_, lean_object* v_rhs_2081_, uint8_t v___x_2082_, lean_object* v___x_2083_, lean_object* v___x_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, uint8_t v___x_2087_, lean_object* v_body_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_ref_2097_; lean_object* v_quotContext_2098_; lean_object* v_currMacroScope_2099_; lean_object* v___x_2100_; 
v_ref_2097_ = lean_ctor_get(v___y_2094_, 5);
lean_inc(v_ref_2097_);
v_quotContext_2098_ = lean_ctor_get(v___y_2094_, 10);
v_currMacroScope_2099_ = lean_ctor_get(v___y_2094_, 11);
lean_inc(v___y_2095_);
lean_inc_ref(v___y_2094_);
lean_inc(v___y_2093_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2090_);
lean_inc_ref(v_a_2080_);
v___x_2100_ = l_Lean_Elab_Term_exprToSyntax(v_a_2080_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v_ref_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v_ref_2102_ = l_Lean_replaceRef(v_rhs_2081_, v_ref_2097_);
v___x_2103_ = l_Lean_SourceInfo_fromRef(v_ref_2102_, v___x_2082_);
lean_dec(v_ref_2102_);
v___x_2104_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0));
lean_inc(v___x_2103_);
v___x_2105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2);
v___x_2107_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3));
lean_inc(v_currMacroScope_2099_);
lean_inc(v_quotContext_2098_);
v___x_2108_ = l_Lean_addMacroScope(v_quotContext_2098_, v___x_2107_, v_currMacroScope_2099_);
v___x_2109_ = lean_box(0);
lean_inc(v___x_2108_);
lean_inc(v___x_2103_);
v___x_2110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2103_);
lean_ctor_set(v___x_2110_, 1, v___x_2106_);
lean_ctor_set(v___x_2110_, 2, v___x_2108_);
lean_ctor_set(v___x_2110_, 3, v___x_2109_);
v___x_2111_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2112_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2111_);
v___x_2113_ = l_Lean_Syntax_node2(v___x_2103_, v___x_2112_, v___x_2105_, v___x_2110_);
v___x_2114_ = l_Lean_SourceInfo_fromRef(v_ref_2097_, v___x_2082_);
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2116_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2115_);
v___x_2117_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6));
lean_inc(v___x_2114_);
v___x_2118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2114_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
lean_inc(v___x_2114_);
v___x_2119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2114_);
lean_ctor_set(v___x_2119_, 1, v___x_2104_);
lean_inc(v___x_2114_);
v___x_2120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2114_);
lean_ctor_set(v___x_2120_, 1, v___x_2106_);
lean_ctor_set(v___x_2120_, 2, v___x_2108_);
lean_ctor_set(v___x_2120_, 3, v___x_2109_);
v___x_2121_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_2114_);
v___x_2122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2114_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_2114_);
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2114_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2126_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2125_);
v___x_2127_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9));
lean_inc(v___x_2114_);
v___x_2128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2114_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2130_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2129_);
lean_inc(v___x_2114_);
v___x_2131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2114_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2133_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_2114_);
v___x_2134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2114_);
lean_ctor_set(v___x_2134_, 1, v___x_2132_);
lean_ctor_set(v___x_2134_, 2, v___x_2133_);
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2136_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_2114_);
v___x_2138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2114_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_inc(v___x_2114_);
v___x_2139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2114_);
lean_ctor_set(v___x_2139_, 1, v___x_2135_);
v___x_2140_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2141_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2140_);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13));
lean_inc(v___x_2114_);
v___x_2143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2114_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2145_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
lean_inc(v___x_2114_);
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2114_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
lean_inc(v___x_2114_);
v___x_2148_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2145_, v___x_2147_);
lean_inc(v___x_2114_);
v___x_2149_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16));
lean_inc(v___x_2114_);
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2114_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
lean_inc_ref(v___x_2134_);
lean_inc(v___x_2114_);
v___x_2152_ = l_Lean_Syntax_node5(v___x_2114_, v___x_2141_, v___x_2143_, v___x_2149_, v___x_2134_, v___x_2151_, v_a_2101_);
v___x_2153_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_2114_);
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2114_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
lean_inc_ref(v___x_2122_);
lean_inc(v___x_2114_);
v___x_2155_ = l_Lean_Syntax_node5(v___x_2114_, v___x_2136_, v___x_2138_, v___x_2139_, v___x_2122_, v___x_2152_, v___x_2154_);
lean_inc(v___x_2114_);
v___x_2156_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2155_);
v___x_2157_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2158_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2157_);
lean_inc_ref(v___x_2134_);
lean_inc(v___x_2114_);
v___x_2159_ = l_Lean_Syntax_node2(v___x_2114_, v___x_2158_, v___x_2134_, v___x_2113_);
lean_inc(v___x_2114_);
v___x_2160_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2159_);
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
lean_inc(v___x_2114_);
v___x_2162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2114_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19));
lean_inc_ref(v___x_2085_);
lean_inc_ref(v___x_2084_);
lean_inc_ref(v___x_2083_);
v___x_2164_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2163_);
v___x_2165_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20));
v___x_2166_ = l_Lean_Name_mkStr4(v___x_2083_, v___x_2084_, v___x_2085_, v___x_2165_);
v___x_2167_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_2114_);
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2114_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
lean_inc(v___x_2114_);
v___x_2169_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2086_);
lean_inc(v___x_2114_);
v___x_2170_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2169_);
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
lean_inc(v___x_2114_);
v___x_2172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2114_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
lean_inc(v___x_2114_);
v___x_2173_ = l_Lean_Syntax_node4(v___x_2114_, v___x_2166_, v___x_2168_, v___x_2170_, v___x_2172_, v_body_2088_);
lean_inc(v___x_2114_);
v___x_2174_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2132_, v___x_2173_);
lean_inc(v___x_2114_);
v___x_2175_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2164_, v___x_2174_);
lean_inc(v___x_2114_);
v___x_2176_ = l_Lean_Syntax_node6(v___x_2114_, v___x_2130_, v___x_2131_, v___x_2134_, v___x_2156_, v___x_2160_, v___x_2162_, v___x_2175_);
lean_inc_ref(v___x_2124_);
lean_inc_ref(v___x_2120_);
lean_inc_ref(v___x_2119_);
lean_inc(v___x_2114_);
v___x_2177_ = l_Lean_Syntax_node5(v___x_2114_, v___x_2126_, v___x_2128_, v___x_2119_, v___x_2120_, v___x_2124_, v___x_2176_);
v___x_2178_ = l_Lean_Syntax_node7(v___x_2114_, v___x_2116_, v___x_2118_, v___x_2119_, v___x_2120_, v___x_2122_, v_rhs_2081_, v___x_2124_, v___x_2177_);
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_a_2080_);
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_box(v___x_2087_);
lean_inc(v___x_2178_);
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 12, 4);
lean_closure_set(v___f_2182_, 0, v___x_2178_);
lean_closure_set(v___f_2182_, 1, v___x_2179_);
lean_closure_set(v___f_2182_, 2, v___x_2181_);
lean_closure_set(v___f_2182_, 3, v___x_2180_);
v___x_2183_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_ref_2097_, v___x_2178_, v___f_2182_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
return v___x_2183_;
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_ref_2097_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v_body_2088_);
lean_dec(v___x_2086_);
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
lean_dec_ref(v___x_2083_);
lean_dec(v_rhs_2081_);
lean_dec_ref(v_a_2080_);
v_a_2184_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2100_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2100_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object** _args){
lean_object* v_a_2192_ = _args[0];
lean_object* v_rhs_2193_ = _args[1];
lean_object* v___x_2194_ = _args[2];
lean_object* v___x_2195_ = _args[3];
lean_object* v___x_2196_ = _args[4];
lean_object* v___x_2197_ = _args[5];
lean_object* v___x_2198_ = _args[6];
lean_object* v___x_2199_ = _args[7];
lean_object* v_body_2200_ = _args[8];
lean_object* v___y_2201_ = _args[9];
lean_object* v___y_2202_ = _args[10];
lean_object* v___y_2203_ = _args[11];
lean_object* v___y_2204_ = _args[12];
lean_object* v___y_2205_ = _args[13];
lean_object* v___y_2206_ = _args[14];
lean_object* v___y_2207_ = _args[15];
lean_object* v___y_2208_ = _args[16];
_start:
{
uint8_t v___x_76296__boxed_2209_; uint8_t v___x_76301__boxed_2210_; lean_object* v_res_2211_; 
v___x_76296__boxed_2209_ = lean_unbox(v___x_2194_);
v___x_76301__boxed_2210_ = lean_unbox(v___x_2199_);
v_res_2211_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_a_2192_, v_rhs_2193_, v___x_76296__boxed_2209_, v___x_2195_, v___x_2196_, v___x_2197_, v___x_2198_, v___x_76301__boxed_2210_, v_body_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0(lean_object* v___x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_quotContext_2216_; lean_object* v_currMacroScope_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_quotContext_2216_ = lean_ctor_get(v___y_2213_, 10);
lean_inc(v_quotContext_2216_);
v_currMacroScope_2217_ = lean_ctor_get(v___y_2213_, 11);
lean_inc(v_currMacroScope_2217_);
lean_dec_ref(v___y_2213_);
v___x_2218_ = l_Lean_addMacroScope(v_quotContext_2216_, v___x_2212_, v_currMacroScope_2217_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0___boxed(lean_object* v___x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0(v___x_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___f_2233_; lean_object* v___x_2234_; 
v___f_2233_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__2));
v___x_2234_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2233_, v___y_2230_, v___y_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___boxed(lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_2235_, v___y_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_ref_2239_, uint8_t v_canonical_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2258_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = l_Lean_mkIdentFrom(v_ref_2239_, v_a_2250_, v_canonical_2240_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2249_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2249_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_ref_2267_, lean_object* v_canonical_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v_canonical_boxed_2277_; lean_object* v_res_2278_; 
v_canonical_boxed_2277_ = lean_unbox(v_canonical_2268_);
v_res_2278_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_ref_2267_, v_canonical_boxed_2277_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_ref_2267_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4(lean_object* v_env_2279_, lean_object* v_options_2280_, lean_object* v_currNamespace_2281_, lean_object* v_openDecls_2282_, lean_object* v_n_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = l_Lean_ResolveName_resolveGlobalName(v_env_2279_, v_options_2280_, v_currNamespace_2281_, v_openDecls_2282_, v_n_2283_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___y_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4___boxed(lean_object* v_env_2288_, lean_object* v_options_2289_, lean_object* v_currNamespace_2290_, lean_object* v_openDecls_2291_, lean_object* v_n_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4(v_env_2288_, v_options_2289_, v_currNamespace_2290_, v_openDecls_2291_, v_n_2292_, v___y_2293_, v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v_options_2289_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = l_Lean_maxRecDepthErrorMessage;
v___x_2302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3);
v___x_2304_ = l_Lean_MessageData_ofFormat(v___x_2303_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4);
v___x_2306_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2));
v___x_2307_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(lean_object* v_ref_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_ref_2308_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___boxed(lean_object* v_ref_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_ref_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3(lean_object* v_currNamespace_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_currNamespace_2316_);
lean_ctor_set(v___x_2319_, 1, v___y_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3___boxed(lean_object* v_currNamespace_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3(v_currNamespace_2320_, v___y_2321_, v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2323_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2324_; double v___x_2325_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_float_of_nat(v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_cls_2328_, lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_ref_2335_; lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2381_; 
v_ref_2335_ = lean_ctor_get(v___y_2332_, 5);
v___x_2336_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2381_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2381_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v_traceState_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_cache_2347_; lean_object* v_messages_2348_; lean_object* v_infoState_2349_; lean_object* v_snapshotTasks_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2380_; 
v___x_2341_ = lean_st_ref_take(v___y_2333_);
v_traceState_2342_ = lean_ctor_get(v___x_2341_, 4);
v_env_2343_ = lean_ctor_get(v___x_2341_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2341_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2341_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2341_, 3);
v_cache_2347_ = lean_ctor_get(v___x_2341_, 5);
v_messages_2348_ = lean_ctor_get(v___x_2341_, 6);
v_infoState_2349_ = lean_ctor_get(v___x_2341_, 7);
v_snapshotTasks_2350_ = lean_ctor_get(v___x_2341_, 8);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2352_ = v___x_2341_;
v_isShared_2353_ = v_isSharedCheck_2380_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_snapshotTasks_2350_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2348_);
lean_inc(v_cache_2347_);
lean_inc(v_traceState_2342_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2341_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2380_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint64_t v_tid_2354_; lean_object* v_traces_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2379_; 
v_tid_2354_ = lean_ctor_get_uint64(v_traceState_2342_, sizeof(void*)*1);
v_traces_2355_ = lean_ctor_get(v_traceState_2342_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_traceState_2342_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2357_ = v_traceState_2342_;
v_isShared_2358_ = v_isSharedCheck_2379_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_traces_2355_);
lean_dec(v_traceState_2342_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2379_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; double v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0);
v___x_2361_ = 0;
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2363_, 0, v_cls_2328_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
lean_ctor_set(v___x_2363_, 2, v___x_2362_);
lean_ctor_set_float(v___x_2363_, sizeof(void*)*3, v___x_2360_);
lean_ctor_set_float(v___x_2363_, sizeof(void*)*3 + 8, v___x_2360_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*3 + 16, v___x_2361_);
v___x_2364_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__1));
v___x_2365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v_a_2337_);
lean_ctor_set(v___x_2365_, 2, v___x_2364_);
lean_inc(v_ref_2335_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_ref_2335_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_PersistentArray_push___redArg(v_traces_2355_, v___x_2366_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2367_);
v___x_2369_ = v___x_2357_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2367_);
lean_ctor_set_uint64(v_reuseFailAlloc_2378_, sizeof(void*)*1, v_tid_2354_);
v___x_2369_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 4, v___x_2369_);
v___x_2371_ = v___x_2352_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_env_2343_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2377_, 5, v_cache_2347_);
lean_ctor_set(v_reuseFailAlloc_2377_, 6, v_messages_2348_);
lean_ctor_set(v_reuseFailAlloc_2377_, 7, v_infoState_2349_);
lean_ctor_set(v_reuseFailAlloc_2377_, 8, v_snapshotTasks_2350_);
v___x_2371_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_st_ref_set(v___y_2333_, v___x_2371_);
v___x_2373_ = lean_box(0);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2373_);
v___x_2375_ = v___x_2339_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_cls_2382_, lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_2382_, v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(lean_object* v_keys_2390_, lean_object* v_i_2391_, lean_object* v_k_2392_){
_start:
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = lean_array_get_size(v_keys_2390_);
v___x_2394_ = lean_nat_dec_lt(v_i_2391_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_dec(v_i_2391_);
return v___x_2394_;
}
else
{
lean_object* v_k_x27_2395_; uint8_t v___x_2396_; 
v_k_x27_2395_ = lean_array_fget_borrowed(v_keys_2390_, v_i_2391_);
v___x_2396_ = l_Lean_instBEqExtraModUse_beq(v_k_2392_, v_k_x27_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_i_2391_, v___x_2397_);
lean_dec(v_i_2391_);
v_i_2391_ = v___x_2398_;
goto _start;
}
else
{
lean_dec(v_i_2391_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg___boxed(lean_object* v_keys_2400_, lean_object* v_i_2401_, lean_object* v_k_2402_){
_start:
{
uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_res_2403_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_keys_2400_, v_i_2401_, v_k_2402_);
lean_dec_ref(v_k_2402_);
lean_dec_ref(v_keys_2400_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(lean_object* v_x_2405_, size_t v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
lean_object* v_es_2408_; lean_object* v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; lean_object* v_j_2413_; lean_object* v___x_2414_; 
v_es_2408_ = lean_ctor_get(v_x_2405_, 0);
lean_inc_ref(v_es_2408_);
lean_dec_ref(v_x_2405_);
v___x_2409_ = lean_box(2);
v___x_2410_ = ((size_t)5ULL);
v___x_2411_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2412_ = lean_usize_land(v_x_2406_, v___x_2411_);
v_j_2413_ = lean_usize_to_nat(v___x_2412_);
v___x_2414_ = lean_array_get(v___x_2409_, v_es_2408_, v_j_2413_);
lean_dec(v_j_2413_);
lean_dec_ref(v_es_2408_);
switch(lean_obj_tag(v___x_2414_))
{
case 0:
{
lean_object* v_key_2415_; uint8_t v___x_2416_; 
v_key_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_key_2415_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = l_Lean_instBEqExtraModUse_beq(v_x_2407_, v_key_2415_);
lean_dec(v_key_2415_);
return v___x_2416_;
}
case 1:
{
lean_object* v_node_2417_; size_t v___x_2418_; 
v_node_2417_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_node_2417_);
lean_dec_ref(v___x_2414_);
v___x_2418_ = lean_usize_shift_right(v_x_2406_, v___x_2410_);
v_x_2405_ = v_node_2417_;
v_x_2406_ = v___x_2418_;
goto _start;
}
default: 
{
uint8_t v___x_2420_; 
v___x_2420_ = 0;
return v___x_2420_;
}
}
}
else
{
lean_object* v_ks_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v_ks_2421_ = lean_ctor_get(v_x_2405_, 0);
lean_inc_ref(v_ks_2421_);
lean_dec_ref(v_x_2405_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_ks_2421_, v___x_2422_, v_x_2407_);
lean_dec_ref(v_ks_2421_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg___boxed(lean_object* v_x_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_){
_start:
{
size_t v_x_76832__boxed_2427_; uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_x_76832__boxed_2427_ = lean_unbox_usize(v_x_2425_);
lean_dec(v_x_2425_);
v_res_2428_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_2424_, v_x_76832__boxed_2427_, v_x_2426_);
lean_dec_ref(v_x_2426_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
uint64_t v___x_2432_; size_t v___x_2433_; uint8_t v___x_2434_; 
v___x_2432_ = l_Lean_instHashableExtraModUse_hash(v_x_2431_);
v___x_2433_ = lean_uint64_to_usize(v___x_2432_);
v___x_2434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_2430_, v___x_2433_, v_x_2431_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg___boxed(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint8_t v_res_2437_; lean_object* v_r_2438_; 
v_res_2437_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v_x_2435_, v_x_2436_);
lean_dec_ref(v_x_2436_);
v_r_2438_ = lean_box(v_res_2437_);
return v_r_2438_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__1));
v___x_2442_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__0));
v___x_2443_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2442_, v___x_2441_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4);
v___x_2450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
lean_ctor_set(v___x_2450_, 2, v___x_2449_);
lean_ctor_set(v___x_2450_, 3, v___x_2449_);
lean_ctor_set(v___x_2450_, 4, v___x_2449_);
lean_ctor_set(v___x_2450_, 5, v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__9));
v___x_2456_ = l_Lean_stringToMessageData(v___x_2455_);
return v___x_2456_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__11));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
return v___x_2461_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__14));
v___x_2464_ = l_Lean_stringToMessageData(v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__16));
v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(lean_object* v_mod_2472_, uint8_t v_isMeta_2473_, lean_object* v_hint_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v_env_2484_; uint8_t v_isExporting_2485_; lean_object* v___x_2486_; lean_object* v_env_2487_; lean_object* v___x_2488_; lean_object* v_entry_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2483_ = lean_st_ref_get(v___y_2481_);
v_env_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_env_2484_);
lean_dec(v___x_2483_);
v_isExporting_2485_ = lean_ctor_get_uint8(v_env_2484_, sizeof(void*)*8);
lean_dec_ref(v_env_2484_);
v___x_2486_ = lean_st_ref_get(v___y_2481_);
v_env_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc_ref(v_env_2487_);
lean_dec(v___x_2486_);
v___x_2488_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2);
lean_inc(v_mod_2472_);
v_entry_2489_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2489_, 0, v_mod_2472_);
lean_ctor_set_uint8(v_entry_2489_, sizeof(void*)*1, v_isExporting_2485_);
lean_ctor_set_uint8(v_entry_2489_, sizeof(void*)*1 + 1, v_isMeta_2473_);
v___x_2490_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2491_ = lean_box(1);
v___x_2492_ = lean_box(0);
v___x_2535_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2488_, v___x_2490_, v_env_2487_, v___x_2491_, v___x_2492_);
v___x_2536_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v___x_2535_, v_entry_2489_);
if (v___x_2536_ == 0)
{
lean_object* v_cls_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2546_; lean_object* v___y_2547_; uint8_t v___x_2559_; 
v_cls_2537_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__8));
v___x_2538_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_2537_, v___y_2480_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v___x_2559_ = lean_unbox(v_a_2539_);
lean_dec(v_a_2539_);
if (v___x_2559_ == 0)
{
lean_dec(v_hint_2474_);
lean_dec(v_mod_2472_);
v___y_2494_ = v___y_2479_;
v___y_2495_ = v___y_2481_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2560_; lean_object* v___y_2562_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15);
if (v_isExporting_2485_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__20));
v___y_2562_ = v___x_2569_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__21));
v___y_2562_ = v___x_2570_;
goto v___jp_2561_;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2563_ = l_Lean_stringToMessageData(v___y_2562_);
v___x_2564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2560_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
if (v_isMeta_2473_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__18));
v___y_2546_ = v___x_2566_;
v___y_2547_ = v___x_2567_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__19));
v___y_2546_ = v___x_2566_;
v___y_2547_ = v___x_2568_;
goto v___jp_2545_;
}
}
}
v___jp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___y_2541_);
lean_ctor_set(v___x_2543_, 1, v___y_2542_);
v___x_2544_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_2537_, v___x_2543_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref(v___x_2544_);
v___y_2494_ = v___y_2479_;
v___y_2495_ = v___y_2481_;
goto v___jp_2493_;
}
else
{
lean_dec_ref(v_entry_2489_);
return v___x_2544_;
}
}
v___jp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2548_ = l_Lean_stringToMessageData(v___y_2547_);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___y_2546_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_MessageData_ofName(v_mod_2472_);
v___x_2553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_Name_isAnonymous(v_hint_2474_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12);
v___x_2556_ = l_Lean_MessageData_ofName(v_hint_2474_);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___y_2541_ = v___x_2553_;
v___y_2542_ = v___x_2557_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2558_; 
lean_dec(v_hint_2474_);
v___x_2558_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13);
v___y_2541_ = v___x_2553_;
v___y_2542_ = v___x_2558_;
goto v___jp_2540_;
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v_entry_2489_);
lean_dec(v_hint_2474_);
lean_dec(v_mod_2472_);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
v___jp_2493_:
{
lean_object* v___x_2496_; lean_object* v_toEnvExtension_2497_; lean_object* v_env_2498_; lean_object* v_nextMacroScope_2499_; lean_object* v_ngen_2500_; lean_object* v_auxDeclNGen_2501_; lean_object* v_traceState_2502_; lean_object* v_messages_2503_; lean_object* v_infoState_2504_; lean_object* v_snapshotTasks_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2533_; 
v___x_2496_ = lean_st_ref_take(v___y_2495_);
v_toEnvExtension_2497_ = lean_ctor_get(v___x_2490_, 0);
lean_inc_ref(v_toEnvExtension_2497_);
v_env_2498_ = lean_ctor_get(v___x_2496_, 0);
v_nextMacroScope_2499_ = lean_ctor_get(v___x_2496_, 1);
v_ngen_2500_ = lean_ctor_get(v___x_2496_, 2);
v_auxDeclNGen_2501_ = lean_ctor_get(v___x_2496_, 3);
v_traceState_2502_ = lean_ctor_get(v___x_2496_, 4);
v_messages_2503_ = lean_ctor_get(v___x_2496_, 6);
v_infoState_2504_ = lean_ctor_get(v___x_2496_, 7);
v_snapshotTasks_2505_ = lean_ctor_get(v___x_2496_, 8);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2496_, 5);
lean_dec(v_unused_2534_);
v___x_2507_ = v___x_2496_;
v_isShared_2508_ = v_isSharedCheck_2533_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_snapshotTasks_2505_);
lean_inc(v_infoState_2504_);
lean_inc(v_messages_2503_);
lean_inc(v_traceState_2502_);
lean_inc(v_auxDeclNGen_2501_);
lean_inc(v_ngen_2500_);
lean_inc(v_nextMacroScope_2499_);
lean_inc(v_env_2498_);
lean_dec(v___x_2496_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2533_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v_asyncMode_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v_asyncMode_2509_ = lean_ctor_get(v_toEnvExtension_2497_, 2);
lean_inc(v_asyncMode_2509_);
lean_dec_ref(v_toEnvExtension_2497_);
v___x_2510_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2490_, v_env_2498_, v_entry_2489_, v_asyncMode_2509_, v___x_2492_);
lean_dec(v_asyncMode_2509_);
v___x_2511_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 5, v___x_2511_);
lean_ctor_set(v___x_2507_, 0, v___x_2510_);
v___x_2513_ = v___x_2507_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_nextMacroScope_2499_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_ngen_2500_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_auxDeclNGen_2501_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_traceState_2502_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_messages_2503_);
lean_ctor_set(v_reuseFailAlloc_2532_, 7, v_infoState_2504_);
lean_ctor_set(v_reuseFailAlloc_2532_, 8, v_snapshotTasks_2505_);
v___x_2513_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_mctx_2516_; lean_object* v_zetaDeltaFVarIds_2517_; lean_object* v_postponed_2518_; lean_object* v_diag_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2530_; 
v___x_2514_ = lean_st_ref_set(v___y_2495_, v___x_2513_);
v___x_2515_ = lean_st_ref_take(v___y_2494_);
v_mctx_2516_ = lean_ctor_get(v___x_2515_, 0);
v_zetaDeltaFVarIds_2517_ = lean_ctor_get(v___x_2515_, 2);
v_postponed_2518_ = lean_ctor_get(v___x_2515_, 3);
v_diag_2519_ = lean_ctor_get(v___x_2515_, 4);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2515_, 1);
lean_dec(v_unused_2531_);
v___x_2521_ = v___x_2515_;
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_diag_2519_);
lean_inc(v_postponed_2518_);
lean_inc(v_zetaDeltaFVarIds_2517_);
lean_inc(v_mctx_2516_);
lean_dec(v___x_2515_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_mctx_2516_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_zetaDeltaFVarIds_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_postponed_2518_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_diag_2519_);
v___x_2525_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_st_ref_set(v___y_2494_, v___x_2525_);
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___boxed(lean_object* v_mod_2573_, lean_object* v_isMeta_2574_, lean_object* v_hint_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v_isMeta_boxed_2584_; lean_object* v_res_2585_; 
v_isMeta_boxed_2584_ = lean_unbox(v_isMeta_2574_);
v_res_2585_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_mod_2573_, v_isMeta_boxed_2584_, v_hint_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(lean_object* v___x_2586_, lean_object* v_declName_2587_, lean_object* v_as_2588_, size_t v_sz_2589_, size_t v_i_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_usize_dec_lt(v_i_2590_, v_sz_2589_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
lean_dec(v_declName_2587_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2591_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v_modules_2603_; lean_object* v___x_2604_; lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v_toImport_2607_; lean_object* v_module_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2602_ = l_Lean_Environment_header(v___x_2586_);
v_modules_2603_ = lean_ctor_get(v___x_2602_, 3);
lean_inc_ref(v_modules_2603_);
lean_dec_ref(v___x_2602_);
v___x_2604_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2605_ = lean_array_uget_borrowed(v_as_2588_, v_i_2590_);
v___x_2606_ = lean_array_get(v___x_2604_, v_modules_2603_, v_a_2605_);
lean_dec_ref(v_modules_2603_);
v_toImport_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_toImport_2607_);
lean_dec(v___x_2606_);
v_module_2608_ = lean_ctor_get(v_toImport_2607_, 0);
lean_inc(v_module_2608_);
lean_dec_ref(v_toImport_2607_);
v___x_2609_ = 0;
lean_inc(v_declName_2587_);
v___x_2610_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_module_2608_, v___x_2609_, v_declName_2587_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2611_; size_t v___x_2612_; size_t v___x_2613_; 
lean_dec_ref(v___x_2610_);
v___x_2611_ = lean_box(0);
v___x_2612_ = ((size_t)1ULL);
v___x_2613_ = lean_usize_add(v_i_2590_, v___x_2612_);
v_i_2590_ = v___x_2613_;
v_b_2591_ = v___x_2611_;
goto _start;
}
else
{
lean_dec(v_declName_2587_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19___boxed(lean_object* v___x_2615_, lean_object* v_declName_2616_, lean_object* v_as_2617_, lean_object* v_sz_2618_, lean_object* v_i_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
size_t v_sz_boxed_2629_; size_t v_i_boxed_2630_; lean_object* v_res_2631_; 
v_sz_boxed_2629_ = lean_unbox_usize(v_sz_2618_);
lean_dec(v_sz_2618_);
v_i_boxed_2630_ = lean_unbox_usize(v_i_2619_);
lean_dec(v_i_2619_);
v_res_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(v___x_2615_, v_declName_2616_, v_as_2617_, v_sz_boxed_2629_, v_i_boxed_2630_, v_b_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v_as_2617_);
lean_dec_ref(v___x_2615_);
return v_res_2631_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__1));
v___x_2635_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__0));
v___x_2636_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(lean_object* v_declName_2639_, uint8_t v_isMeta_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v_env_2653_; lean_object* v___y_2655_; lean_object* v___x_2668_; 
v___x_2649_ = lean_st_ref_get(v___y_2647_);
v_env_2653_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2653_);
lean_dec(v___x_2649_);
v___x_2668_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2653_, v_declName_2639_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref(v_env_2653_);
lean_dec(v_declName_2639_);
goto v___jp_2650_;
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2670_; lean_object* v_modules_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = l_Lean_Environment_header(v_env_2653_);
v_modules_2671_ = lean_ctor_get(v___x_2670_, 3);
lean_inc_ref(v_modules_2671_);
lean_dec_ref(v___x_2670_);
v___x_2672_ = lean_array_get_size(v_modules_2671_);
v___x_2673_ = lean_nat_dec_lt(v_val_2669_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_dec_ref(v_modules_2671_);
lean_dec(v_val_2669_);
lean_dec_ref(v_env_2653_);
lean_dec(v_declName_2639_);
goto v___jp_2650_;
}
else
{
lean_object* v___x_2674_; lean_object* v_env_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___y_2679_; 
v___x_2674_ = lean_st_ref_get(v___y_2647_);
v_env_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2674_);
v___x_2676_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2);
v___x_2677_ = lean_array_fget(v_modules_2671_, v_val_2669_);
lean_dec(v_val_2669_);
lean_dec_ref(v_modules_2671_);
if (v_isMeta_2640_ == 0)
{
lean_dec_ref(v_env_2675_);
v___y_2679_ = v_isMeta_2640_;
goto v___jp_2678_;
}
else
{
uint8_t v___x_2690_; 
lean_inc(v_declName_2639_);
v___x_2690_ = l_Lean_isMarkedMeta(v_env_2675_, v_declName_2639_);
if (v___x_2690_ == 0)
{
v___y_2679_ = v_isMeta_2640_;
goto v___jp_2678_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
v___y_2679_ = v___x_2691_;
goto v___jp_2678_;
}
}
v___jp_2678_:
{
lean_object* v_toImport_2680_; lean_object* v_module_2681_; lean_object* v___x_2682_; 
v_toImport_2680_ = lean_ctor_get(v___x_2677_, 0);
lean_inc_ref(v_toImport_2680_);
lean_dec(v___x_2677_);
v_module_2681_ = lean_ctor_get(v_toImport_2680_, 0);
lean_inc(v_module_2681_);
lean_dec_ref(v_toImport_2680_);
lean_inc(v_declName_2639_);
v___x_2682_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_module_2681_, v___y_2679_, v_declName_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v___x_2682_);
v___x_2683_ = l_Lean_indirectModUseExt;
v___x_2684_ = lean_box(1);
v___x_2685_ = lean_box(0);
lean_inc_ref(v_env_2653_);
v___x_2686_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2676_, v___x_2683_, v_env_2653_, v___x_2684_, v___x_2685_);
v___x_2687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_2686_, v_declName_2639_);
lean_dec(v___x_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__3));
v___y_2655_ = v___x_2688_;
goto v___jp_2654_;
}
else
{
lean_object* v_val_2689_; 
v_val_2689_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2689_);
lean_dec_ref(v___x_2687_);
v___y_2655_ = v_val_2689_;
goto v___jp_2654_;
}
}
else
{
lean_dec_ref(v_env_2653_);
lean_dec(v_declName_2639_);
return v___x_2682_;
}
}
}
}
v___jp_2650_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
return v___x_2652_;
}
v___jp_2654_:
{
lean_object* v___x_2656_; size_t v_sz_2657_; size_t v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_box(0);
v_sz_2657_ = lean_array_size(v___y_2655_);
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(v_env_2653_, v_declName_2639_, v___y_2655_, v_sz_2657_, v___x_2658_, v___x_2656_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v_env_2653_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2656_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2656_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___boxed(lean_object* v_declName_2692_, lean_object* v_isMeta_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
uint8_t v_isMeta_boxed_2702_; lean_object* v_res_2703_; 
v_isMeta_boxed_2702_ = lean_unbox(v_isMeta_2693_);
v_res_2703_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(v_declName_2692_, v_isMeta_boxed_2702_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(lean_object* v_as_x27_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
if (lean_obj_tag(v_as_x27_2704_) == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_b_2705_);
return v___x_2714_;
}
else
{
lean_object* v_head_2715_; lean_object* v_tail_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v_head_2715_ = lean_ctor_get(v_as_x27_2704_, 0);
lean_inc(v_head_2715_);
v_tail_2716_ = lean_ctor_get(v_as_x27_2704_, 1);
lean_inc(v_tail_2716_);
lean_dec_ref(v_as_x27_2704_);
v___x_2717_ = 1;
v___x_2718_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(v_head_2715_, v___x_2717_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; 
lean_dec_ref(v___x_2718_);
v___x_2719_ = lean_box(0);
v_as_x27_2704_ = v_tail_2716_;
v_b_2705_ = v___x_2719_;
goto _start;
}
else
{
lean_dec(v_tail_2716_);
return v___x_2718_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg___boxed(lean_object* v_as_x27_2721_, lean_object* v_b_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_as_x27_2721_, v_b_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(lean_object* v_x_2732_, lean_object* v___y_2733_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; 
v_a_2734_ = lean_ctor_get(v_x_2732_, 0);
lean_inc(v_a_2734_);
v___x_2735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_a_2734_);
lean_ctor_set(v___x_2735_, 1, v___y_2733_);
return v___x_2735_;
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v_x_2732_, 0);
lean_inc(v_a_2736_);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2736_);
lean_ctor_set(v___x_2737_, 1, v___y_2733_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg___boxed(lean_object* v_x_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v_x_2738_, v___y_2739_);
lean_dec_ref(v_x_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0(lean_object* v_env_2741_, lean_object* v_stx_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2741_, v_stx_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
if (lean_obj_tag(v_a_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
v_a_2747_ = lean_ctor_get(v___x_2745_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2745_, 0);
lean_dec(v_unused_2756_);
v___x_2749_ = v___x_2745_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2745_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_box(0);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_a_2747_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_val_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2785_; 
v_val_2757_ = lean_ctor_get(v_a_2746_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_a_2746_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2759_ = v_a_2746_;
v_isShared_2760_ = v_isSharedCheck_2785_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_val_2757_);
lean_dec(v_a_2746_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2785_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v_snd_2761_; 
v_snd_2761_ = lean_ctor_get(v_val_2757_, 1);
lean_inc(v_snd_2761_);
lean_dec(v_val_2757_);
if (lean_obj_tag(v_snd_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2771_; 
lean_del_object(v___x_2759_);
v_a_2762_ = lean_ctor_get(v___x_2745_, 1);
lean_inc(v_a_2762_);
lean_dec_ref(v___x_2745_);
v_a_2763_ = lean_ctor_get(v_snd_2761_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_snd_2761_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2765_ = v_snd_2761_;
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v_snd_2761_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v___x_2768_, v_a_2762_);
lean_dec_ref(v___x_2768_);
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2784_; 
v_a_2772_ = lean_ctor_get(v___x_2745_, 1);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2745_);
v_a_2773_ = lean_ctor_get(v_snd_2761_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_snd_2761_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2775_ = v_snd_2761_;
v_isShared_2776_ = v_isSharedCheck_2784_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v_snd_2761_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2784_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v_a_2773_);
v___x_2778_ = v___x_2759_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2780_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2778_);
v___x_2780_ = v___x_2775_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v___x_2780_, v_a_2772_);
lean_dec_ref(v___x_2780_);
return v___x_2781_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_a_2786_ = lean_ctor_get(v___x_2745_, 0);
v_a_2787_ = lean_ctor_get(v___x_2745_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2745_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_inc(v_a_2786_);
lean_dec(v___x_2745_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2786_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0___boxed(lean_object* v_env_2795_, lean_object* v_stx_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0(v_env_2795_, v_stx_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2(lean_object* v_env_2800_, lean_object* v_currNamespace_2801_, lean_object* v_openDecls_2802_, lean_object* v_n_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = l_Lean_ResolveName_resolveNamespace(v_env_2800_, v_currNamespace_2801_, v_openDecls_2802_, v_n_2803_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___y_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2___boxed(lean_object* v_env_2808_, lean_object* v_currNamespace_2809_, lean_object* v_openDecls_2810_, lean_object* v_n_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2(v_env_2808_, v_currNamespace_2809_, v_openDecls_2810_, v_n_2811_, v___y_2812_, v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(lean_object* v_msg_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_ref_2821_; lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2831_; 
v_ref_2821_ = lean_ctor_get(v___y_2818_, 5);
v___x_2822_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2831_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_inc(v_ref_2821_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_ref_2821_);
lean_ctor_set(v___x_2827_, 1, v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
lean_ctor_set(v___x_2825_, 0, v___x_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_msg_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(lean_object* v_ref_2839_, lean_object* v_msg_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_fileName_2849_; lean_object* v_fileMap_2850_; lean_object* v_options_2851_; lean_object* v_currRecDepth_2852_; lean_object* v_maxRecDepth_2853_; lean_object* v_ref_2854_; lean_object* v_currNamespace_2855_; lean_object* v_openDecls_2856_; lean_object* v_initHeartbeats_2857_; lean_object* v_maxHeartbeats_2858_; lean_object* v_quotContext_2859_; lean_object* v_currMacroScope_2860_; uint8_t v_diag_2861_; lean_object* v_cancelTk_x3f_2862_; uint8_t v_suppressElabErrors_2863_; lean_object* v_inheritedTraceOptions_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2873_; 
v_fileName_2849_ = lean_ctor_get(v___y_2846_, 0);
v_fileMap_2850_ = lean_ctor_get(v___y_2846_, 1);
v_options_2851_ = lean_ctor_get(v___y_2846_, 2);
v_currRecDepth_2852_ = lean_ctor_get(v___y_2846_, 3);
v_maxRecDepth_2853_ = lean_ctor_get(v___y_2846_, 4);
v_ref_2854_ = lean_ctor_get(v___y_2846_, 5);
v_currNamespace_2855_ = lean_ctor_get(v___y_2846_, 6);
v_openDecls_2856_ = lean_ctor_get(v___y_2846_, 7);
v_initHeartbeats_2857_ = lean_ctor_get(v___y_2846_, 8);
v_maxHeartbeats_2858_ = lean_ctor_get(v___y_2846_, 9);
v_quotContext_2859_ = lean_ctor_get(v___y_2846_, 10);
v_currMacroScope_2860_ = lean_ctor_get(v___y_2846_, 11);
v_diag_2861_ = lean_ctor_get_uint8(v___y_2846_, sizeof(void*)*14);
v_cancelTk_x3f_2862_ = lean_ctor_get(v___y_2846_, 12);
v_suppressElabErrors_2863_ = lean_ctor_get_uint8(v___y_2846_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2864_ = lean_ctor_get(v___y_2846_, 13);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___y_2846_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2866_ = v___y_2846_;
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_inheritedTraceOptions_2864_);
lean_inc(v_cancelTk_x3f_2862_);
lean_inc(v_currMacroScope_2860_);
lean_inc(v_quotContext_2859_);
lean_inc(v_maxHeartbeats_2858_);
lean_inc(v_initHeartbeats_2857_);
lean_inc(v_openDecls_2856_);
lean_inc(v_currNamespace_2855_);
lean_inc(v_ref_2854_);
lean_inc(v_maxRecDepth_2853_);
lean_inc(v_currRecDepth_2852_);
lean_inc(v_options_2851_);
lean_inc(v_fileMap_2850_);
lean_inc(v_fileName_2849_);
lean_dec(v___y_2846_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_ref_2868_; lean_object* v___x_2870_; 
v_ref_2868_ = l_Lean_replaceRef(v_ref_2839_, v_ref_2854_);
lean_dec(v_ref_2854_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 5, v_ref_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_fileName_2849_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_fileMap_2850_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_options_2851_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_currRecDepth_2852_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_maxRecDepth_2853_);
lean_ctor_set(v_reuseFailAlloc_2872_, 5, v_ref_2868_);
lean_ctor_set(v_reuseFailAlloc_2872_, 6, v_currNamespace_2855_);
lean_ctor_set(v_reuseFailAlloc_2872_, 7, v_openDecls_2856_);
lean_ctor_set(v_reuseFailAlloc_2872_, 8, v_initHeartbeats_2857_);
lean_ctor_set(v_reuseFailAlloc_2872_, 9, v_maxHeartbeats_2858_);
lean_ctor_set(v_reuseFailAlloc_2872_, 10, v_quotContext_2859_);
lean_ctor_set(v_reuseFailAlloc_2872_, 11, v_currMacroScope_2860_);
lean_ctor_set(v_reuseFailAlloc_2872_, 12, v_cancelTk_x3f_2862_);
lean_ctor_set(v_reuseFailAlloc_2872_, 13, v_inheritedTraceOptions_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*14, v_diag_2861_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*14 + 1, v_suppressElabErrors_2863_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_2840_, v___y_2844_, v___y_2845_, v___x_2870_, v___y_2847_);
lean_dec_ref(v___x_2870_);
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg___boxed(lean_object* v_ref_2874_, lean_object* v_msg_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_ref_2874_, v_msg_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_ref_2874_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(lean_object* v_as_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
if (lean_obj_tag(v_as_2885_) == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_box(0);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
else
{
lean_object* v_head_2896_; lean_object* v_tail_2897_; lean_object* v_fst_2898_; lean_object* v_snd_2899_; lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2913_; 
v_head_2896_ = lean_ctor_get(v_as_2885_, 0);
lean_inc(v_head_2896_);
v_tail_2897_ = lean_ctor_get(v_as_2885_, 1);
lean_inc(v_tail_2897_);
lean_dec_ref(v_as_2885_);
v_fst_2898_ = lean_ctor_get(v_head_2896_, 0);
lean_inc(v_fst_2898_);
v_snd_2899_ = lean_ctor_get(v_head_2896_, 1);
lean_inc(v_snd_2899_);
lean_dec(v_head_2896_);
lean_inc(v_fst_2898_);
v___x_2900_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_2898_, v___y_2891_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_unbox(v_a_2901_);
lean_dec(v_a_2901_);
if (v___x_2905_ == 0)
{
lean_del_object(v___x_2903_);
lean_dec(v_snd_2899_);
lean_dec(v_fst_2898_);
v_as_2885_ = v_tail_2897_;
goto _start;
}
else
{
lean_object* v___x_2908_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 3);
lean_ctor_set(v___x_2903_, 0, v_snd_2899_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_snd_2899_);
v___x_2908_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = l_Lean_MessageData_ofFormat(v___x_2908_);
v___x_2910_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_fst_2898_, v___x_2909_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_dec_ref(v___x_2910_);
v_as_2885_ = v_tail_2897_;
goto _start;
}
else
{
lean_dec(v_tail_2897_);
return v___x_2910_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16___boxed(lean_object* v_as_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(v_as_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1(lean_object* v_env_2924_, lean_object* v_declName_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v___x_2928_; lean_object* v_env_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; 
v___x_2928_ = 0;
v_env_2929_ = l_Lean_Environment_setExporting(v_env_2924_, v___x_2928_);
lean_inc(v_declName_2925_);
v___x_2930_ = l_Lean_mkPrivateName(v_env_2929_, v_declName_2925_);
v___x_2931_ = 1;
lean_inc_ref(v_env_2929_);
v___x_2932_ = l_Lean_Environment_contains(v_env_2929_, v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = l_Lean_privateToUserName(v_declName_2925_);
v___x_2934_ = l_Lean_Environment_contains(v_env_2929_, v___x_2933_, v___x_2931_);
v___x_2935_ = lean_box(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
lean_ctor_set(v___x_2936_, 1, v___y_2927_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec_ref(v_env_2929_);
lean_dec(v_declName_2925_);
v___x_2937_ = lean_box(v___x_2932_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___y_2927_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1___boxed(lean_object* v_env_2939_, lean_object* v_declName_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1(v_env_2939_, v_declName_2940_, v___y_2941_, v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(lean_object* v_x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v_env_2955_; lean_object* v_options_2956_; lean_object* v_currRecDepth_2957_; lean_object* v_maxRecDepth_2958_; lean_object* v_ref_2959_; lean_object* v_currNamespace_2960_; lean_object* v_openDecls_2961_; lean_object* v_quotContext_2962_; lean_object* v_currMacroScope_2963_; lean_object* v___x_2964_; lean_object* v_nextMacroScope_2965_; lean_object* v___f_2966_; lean_object* v___f_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v_methods_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2954_ = lean_st_ref_get(v___y_2952_);
v_env_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_env_2955_);
lean_dec(v___x_2954_);
v_options_2956_ = lean_ctor_get(v___y_2951_, 2);
v_currRecDepth_2957_ = lean_ctor_get(v___y_2951_, 3);
v_maxRecDepth_2958_ = lean_ctor_get(v___y_2951_, 4);
v_ref_2959_ = lean_ctor_get(v___y_2951_, 5);
v_currNamespace_2960_ = lean_ctor_get(v___y_2951_, 6);
v_openDecls_2961_ = lean_ctor_get(v___y_2951_, 7);
v_quotContext_2962_ = lean_ctor_get(v___y_2951_, 10);
v_currMacroScope_2963_ = lean_ctor_get(v___y_2951_, 11);
v___x_2964_ = lean_st_ref_get(v___y_2952_);
v_nextMacroScope_2965_ = lean_ctor_get(v___x_2964_, 1);
lean_inc(v_nextMacroScope_2965_);
lean_dec(v___x_2964_);
lean_inc_ref(v_env_2955_);
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2966_, 0, v_env_2955_);
lean_inc_ref(v_env_2955_);
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2967_, 0, v_env_2955_);
lean_inc(v_openDecls_2961_);
lean_inc(v_currNamespace_2960_);
lean_inc_ref(v_env_2955_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2968_, 0, v_env_2955_);
lean_closure_set(v___f_2968_, 1, v_currNamespace_2960_);
lean_closure_set(v___f_2968_, 2, v_openDecls_2961_);
lean_inc(v_currNamespace_2960_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2969_, 0, v_currNamespace_2960_);
lean_inc(v_openDecls_2961_);
lean_inc(v_currNamespace_2960_);
lean_inc_ref(v_options_2956_);
v___f_2970_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2970_, 0, v_env_2955_);
lean_closure_set(v___f_2970_, 1, v_options_2956_);
lean_closure_set(v___f_2970_, 2, v_currNamespace_2960_);
lean_closure_set(v___f_2970_, 3, v_openDecls_2961_);
v_methods_2971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2971_, 0, v___f_2966_);
lean_ctor_set(v_methods_2971_, 1, v___f_2969_);
lean_ctor_set(v_methods_2971_, 2, v___f_2967_);
lean_ctor_set(v_methods_2971_, 3, v___f_2968_);
lean_ctor_set(v_methods_2971_, 4, v___f_2970_);
lean_inc(v_ref_2959_);
lean_inc(v_maxRecDepth_2958_);
lean_inc(v_currRecDepth_2957_);
lean_inc(v_currMacroScope_2963_);
lean_inc(v_quotContext_2962_);
v___x_2972_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2972_, 0, v_methods_2971_);
lean_ctor_set(v___x_2972_, 1, v_quotContext_2962_);
lean_ctor_set(v___x_2972_, 2, v_currMacroScope_2963_);
lean_ctor_set(v___x_2972_, 3, v_currRecDepth_2957_);
lean_ctor_set(v___x_2972_, 4, v_maxRecDepth_2958_);
lean_ctor_set(v___x_2972_, 5, v_ref_2959_);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2974_, 0, v_nextMacroScope_2965_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
v___x_2975_ = lean_apply_2(v_x_2945_, v___x_2972_, v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v_a_2977_; lean_object* v_macroScope_2978_; lean_object* v_traceMsgs_2979_; lean_object* v_expandedMacroDecls_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 1);
lean_inc(v_a_2976_);
v_a_2977_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2975_);
v_macroScope_2978_ = lean_ctor_get(v_a_2976_, 0);
lean_inc(v_macroScope_2978_);
v_traceMsgs_2979_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_traceMsgs_2979_);
v_expandedMacroDecls_2980_ = lean_ctor_get(v_a_2976_, 2);
lean_inc(v_expandedMacroDecls_2980_);
lean_dec(v_a_2976_);
v___x_2981_ = lean_box(0);
v___x_2982_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_expandedMacroDecls_2980_, v___x_2981_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v_ngen_2985_; lean_object* v_auxDeclNGen_2986_; lean_object* v_traceState_2987_; lean_object* v_cache_2988_; lean_object* v_messages_2989_; lean_object* v_infoState_2990_; lean_object* v_snapshotTasks_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v___x_2982_);
v___x_2983_ = lean_st_ref_take(v___y_2952_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
v_ngen_2985_ = lean_ctor_get(v___x_2983_, 2);
v_auxDeclNGen_2986_ = lean_ctor_get(v___x_2983_, 3);
v_traceState_2987_ = lean_ctor_get(v___x_2983_, 4);
v_cache_2988_ = lean_ctor_get(v___x_2983_, 5);
v_messages_2989_ = lean_ctor_get(v___x_2983_, 6);
v_infoState_2990_ = lean_ctor_get(v___x_2983_, 7);
v_snapshotTasks_2991_ = lean_ctor_get(v___x_2983_, 8);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_2983_, 1);
lean_dec(v_unused_3018_);
v___x_2993_ = v___x_2983_;
v_isShared_2994_ = v_isSharedCheck_3017_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snapshotTasks_2991_);
lean_inc(v_infoState_2990_);
lean_inc(v_messages_2989_);
lean_inc(v_cache_2988_);
lean_inc(v_traceState_2987_);
lean_inc(v_auxDeclNGen_2986_);
lean_inc(v_ngen_2985_);
lean_inc(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3017_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_macroScope_2978_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_env_2984_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_macroScope_2978_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_ngen_2985_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_auxDeclNGen_2986_);
lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_traceState_2987_);
lean_ctor_set(v_reuseFailAlloc_3016_, 5, v_cache_2988_);
lean_ctor_set(v_reuseFailAlloc_3016_, 6, v_messages_2989_);
lean_ctor_set(v_reuseFailAlloc_3016_, 7, v_infoState_2990_);
lean_ctor_set(v_reuseFailAlloc_3016_, 8, v_snapshotTasks_2991_);
v___x_2996_ = v_reuseFailAlloc_3016_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_st_ref_set(v___y_2952_, v___x_2996_);
v___x_2998_ = l_List_reverse___redArg(v_traceMsgs_2979_);
v___x_2999_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(v___x_2998_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec_ref(v___y_2951_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3007_);
v___x_3001_ = v___x_2999_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v___x_2999_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v_a_2977_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2977_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_a_2977_);
v_a_3008_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2999_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2999_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_traceMsgs_2979_);
lean_dec(v_macroScope_2978_);
lean_dec(v_a_2977_);
lean_dec_ref(v___y_2951_);
v_a_3019_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2982_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2982_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; 
v_a_3027_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_3027_);
lean_dec_ref(v___x_2975_);
if (lean_obj_tag(v_a_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v_a_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_a_3028_ = lean_ctor_get(v_a_3027_, 0);
lean_inc(v_a_3028_);
v_a_3029_ = lean_ctor_get(v_a_3027_, 1);
lean_inc_ref(v_a_3029_);
lean_dec_ref(v_a_3027_);
v___x_3030_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___closed__0));
v___x_3031_ = lean_string_dec_eq(v_a_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3029_);
v___x_3033_ = l_Lean_MessageData_ofFormat(v___x_3032_);
v___x_3034_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_a_3028_, v___x_3033_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v_a_3028_);
return v___x_3034_;
}
else
{
lean_object* v___x_3035_; 
lean_dec_ref(v_a_3029_);
lean_dec_ref(v___y_2951_);
v___x_3035_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_a_3028_);
return v___x_3035_;
}
}
else
{
lean_object* v___x_3036_; 
lean_dec_ref(v___y_2951_);
v___x_3036_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___boxed(lean_object* v_x_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v_x_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3046_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__5(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__4));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__7(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__6));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__9(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__8));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_letOrReassign_3067_, lean_object* v_decl_3068_, lean_object* v_dec_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_letOrReassign_3067_, v_decl_3068_, v_dec_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_letOrReassign_3079_, lean_object* v_decl_3080_, lean_object* v_dec_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v___x_3090_; 
lean_inc(v_a_3088_);
lean_inc_ref(v_a_3087_);
lean_inc(v_a_3086_);
lean_inc_ref(v_a_3085_);
lean_inc(v_a_3084_);
lean_inc_ref(v_a_3083_);
lean_inc(v_decl_3080_);
v___x_3090_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3080_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
lean_inc_ref(v_a_3087_);
v___x_3092_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3079_, v_a_3091_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3093_; 
lean_dec_ref(v___x_3092_);
lean_inc(v_a_3088_);
lean_inc_ref(v_a_3087_);
lean_inc(v_a_3086_);
lean_inc_ref(v_a_3085_);
lean_inc(v_a_3084_);
lean_inc_ref(v_a_3083_);
v___x_3093_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3079_, v_decl_3080_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_doBlockResultType_3095_; lean_object* v___x_3096_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref(v___x_3093_);
v_doBlockResultType_3095_ = lean_ctor_get(v_a_3082_, 3);
lean_inc_ref(v_a_3082_);
lean_inc_ref(v_doBlockResultType_3095_);
v___x_3096_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_3095_, v_a_3082_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3301_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3301_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3301_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3101_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3103_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3104_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3094_);
v___x_3105_ = l_Lean_Syntax_isOfKind(v_a_3094_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_dec(v_a_3094_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v___x_3106_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = l_Lean_Syntax_getArg(v_a_3094_, v___x_3107_);
lean_dec(v_a_3094_);
v___x_3109_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3108_);
v___x_3110_ = l_Lean_Syntax_isOfKind(v___x_3108_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3108_);
v___x_3112_ = l_Lean_Syntax_isOfKind(v___x_3108_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; uint8_t v___x_3114_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
v___x_3113_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3108_);
v___x_3114_ = l_Lean_Syntax_isOfKind(v___x_3108_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; 
lean_dec(v___x_3108_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v___x_3115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3115_;
}
else
{
lean_object* v___x_3116_; lean_object* v_id_3117_; lean_object* v_binders_3118_; lean_object* v_type_3119_; lean_object* v_value_3120_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; uint8_t v___y_3131_; lean_object* v_id_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___x_3199_; 
v___x_3116_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3108_);
lean_dec(v___x_3108_);
v_id_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_id_3117_);
v_binders_3118_ = lean_ctor_get(v___x_3116_, 1);
lean_inc_ref(v_binders_3118_);
v_type_3119_ = lean_ctor_get(v___x_3116_, 2);
lean_inc(v_type_3119_);
v_value_3120_ = lean_ctor_get(v___x_3116_, 3);
lean_inc(v_value_3120_);
lean_dec_ref(v___x_3116_);
v___x_3199_ = l_Lean_Syntax_isIdent(v_id_3117_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_inc(v_a_3088_);
lean_inc_ref(v_a_3087_);
v___x_3200_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_id_3117_, v___x_3105_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_id_3117_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref(v___x_3200_);
v_id_3189_ = v_a_3201_;
v___y_3190_ = v_a_3082_;
v___y_3191_ = v_a_3083_;
v___y_3192_ = v_a_3084_;
v___y_3193_ = v_a_3085_;
v___y_3194_ = v_a_3086_;
v___y_3195_ = v_a_3087_;
v___y_3196_ = v_a_3088_;
goto v___jp_3188_;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_value_3120_);
lean_dec(v_type_3119_);
lean_dec_ref(v_binders_3118_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v_a_3202_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3200_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3200_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
v_id_3189_ = v_id_3117_;
v___y_3190_ = v_a_3082_;
v___y_3191_ = v_a_3083_;
v___y_3192_ = v_a_3084_;
v___y_3193_ = v_a_3085_;
v___y_3194_ = v_a_3086_;
v___y_3195_ = v_a_3087_;
v___y_3196_ = v_a_3088_;
goto v___jp_3188_;
}
v___jp_3121_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; 
v___x_3132_ = lean_box(v___x_3105_);
v___x_3133_ = lean_box(v___x_3110_);
v___x_3134_ = lean_box(v___y_3131_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3135_, 0, v_type_3119_);
lean_closure_set(v___f_3135_, 1, v_value_3120_);
lean_closure_set(v___f_3135_, 2, v___x_3132_);
lean_closure_set(v___f_3135_, 3, v___x_3133_);
lean_closure_set(v___f_3135_, 4, v___x_3107_);
lean_closure_set(v___f_3135_, 5, v___x_3134_);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3123_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3126_);
v___x_3136_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3118_, v___f_3135_, v___y_3126_, v___y_3124_, v___y_3123_, v___y_3125_, v___y_3130_, v___y_3128_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v_fst_3138_; lean_object* v_snd_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3179_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3136_);
v_fst_3138_ = lean_ctor_get(v_a_3137_, 0);
v_snd_3139_ = lean_ctor_get(v_a_3137_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_a_3137_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3141_ = v_a_3137_;
v_isShared_3142_ = v_isSharedCheck_3179_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_snd_3139_);
lean_inc(v_fst_3138_);
lean_dec(v_a_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3179_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3144_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3143_, v___y_3130_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; uint8_t v___x_3148_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = l_Lean_Syntax_getId(v___y_3127_);
lean_dec(v___y_3127_);
v___x_3147_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3146_);
v___x_3148_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; 
lean_del_object(v___x_3141_);
v___x_3149_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3146_, v_fst_3138_, v_snd_3139_, v___y_3122_, v___y_3131_, v___x_3147_, v___y_3129_, v___y_3126_, v___y_3124_, v___y_3123_, v___y_3125_, v___y_3130_, v___y_3128_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_inc(v___x_3146_);
v___x_3150_ = l_Lean_MessageData_ofName(v___x_3146_);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__5);
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 7);
lean_ctor_set(v___x_3141_, 1, v___x_3151_);
lean_ctor_set(v___x_3141_, 0, v___x_3150_);
v___x_3153_ = v___x_3141_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_inc(v_fst_3138_);
v___x_3154_ = l_Lean_MessageData_ofExpr(v_fst_3138_);
v___x_3155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__7, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__7);
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
lean_inc(v_snd_3139_);
v___x_3158_ = l_Lean_MessageData_ofExpr(v_snd_3139_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3143_, v___x_3159_, v___y_3123_, v___y_3125_, v___y_3130_, v___y_3128_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v___x_3160_);
v___x_3161_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3146_, v_fst_3138_, v_snd_3139_, v___y_3122_, v___y_3131_, v___x_3147_, v___y_3129_, v___y_3126_, v___y_3124_, v___y_3123_, v___y_3125_, v___y_3130_, v___y_3128_);
return v___x_3161_;
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v___x_3146_);
lean_dec(v_snd_3139_);
lean_dec(v_fst_3138_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
v_a_3162_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3160_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3160_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_del_object(v___x_3141_);
lean_dec(v_snd_3139_);
lean_dec(v_fst_3138_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
v_a_3171_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3144_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3144_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
v_a_3180_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3136_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3136_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
v___jp_3188_:
{
lean_object* v___x_3197_; lean_object* v___f_3198_; 
v___x_3197_ = lean_box(v___x_3110_);
lean_inc(v_letOrReassign_3079_);
lean_inc(v_id_3189_);
v___f_3198_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 14, 5);
lean_closure_set(v___f_3198_, 0, v_id_3189_);
lean_closure_set(v___f_3198_, 1, v_dec_3081_);
lean_closure_set(v___f_3198_, 2, v___x_3197_);
lean_closure_set(v___f_3198_, 3, v_letOrReassign_3079_);
lean_closure_set(v___f_3198_, 4, v_a_3091_);
if (lean_obj_tag(v_letOrReassign_3079_) == 1)
{
v___y_3122_ = v___f_3198_;
v___y_3123_ = v___y_3193_;
v___y_3124_ = v___y_3192_;
v___y_3125_ = v___y_3194_;
v___y_3126_ = v___y_3191_;
v___y_3127_ = v_id_3189_;
v___y_3128_ = v___y_3196_;
v___y_3129_ = v___y_3190_;
v___y_3130_ = v___y_3195_;
v___y_3131_ = v___x_3105_;
goto v___jp_3121_;
}
else
{
lean_dec(v_letOrReassign_3079_);
v___y_3122_ = v___f_3198_;
v___y_3123_ = v___y_3193_;
v___y_3124_ = v___y_3192_;
v___y_3125_ = v___y_3194_;
v___y_3126_ = v___y_3191_;
v___y_3127_ = v_id_3189_;
v___y_3128_ = v___y_3196_;
v___y_3129_ = v___y_3190_;
v___y_3130_ = v___y_3195_;
v___y_3131_ = v___x_3110_;
goto v___jp_3121_;
}
}
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = l_Lean_Syntax_getArg(v___x_3108_, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_matchesNull(v___x_3211_, v___x_3107_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec(v___x_3108_);
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v___x_3213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; lean_object* v_rhs_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v_xType_x3f_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3214_ = l_Lean_Syntax_getArg(v___x_3108_, v___x_3107_);
v___x_3269_ = lean_unsigned_to_nat(2u);
v___x_3270_ = l_Lean_Syntax_getArg(v___x_3108_, v___x_3269_);
v___x_3271_ = l_Lean_Syntax_isNone(v___x_3270_);
if (v___x_3271_ == 0)
{
uint8_t v___x_3272_; 
lean_inc(v___x_3270_);
v___x_3272_ = l_Lean_Syntax_matchesNull(v___x_3270_, v___x_3210_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_dec(v___x_3270_);
lean_dec(v___x_3214_);
lean_dec(v___x_3108_);
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v___x_3273_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = l_Lean_Syntax_getArg(v___x_3270_, v___x_3107_);
lean_dec(v___x_3270_);
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3274_);
v___x_3276_ = l_Lean_Syntax_isOfKind(v___x_3274_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; 
lean_dec(v___x_3274_);
lean_dec(v___x_3214_);
lean_dec(v___x_3108_);
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v___x_3277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3278_ = l_Lean_Syntax_getArg(v___x_3274_, v___x_3210_);
lean_dec(v___x_3274_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 1);
lean_ctor_set(v___x_3099_, 0, v___x_3278_);
v___x_3280_ = v___x_3099_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v_xType_x3f_3235_ = v___x_3280_;
v___y_3236_ = v_a_3082_;
v___y_3237_ = v_a_3083_;
v___y_3238_ = v_a_3084_;
v___y_3239_ = v_a_3085_;
v___y_3240_ = v_a_3086_;
v___y_3241_ = v_a_3087_;
v___y_3242_ = v_a_3088_;
goto v___jp_3234_;
}
}
}
}
else
{
lean_object* v___x_3282_; 
lean_dec(v___x_3270_);
lean_del_object(v___x_3099_);
v___x_3282_ = lean_box(0);
v_xType_x3f_3235_ = v___x_3282_;
v___y_3236_ = v_a_3082_;
v___y_3237_ = v_a_3083_;
v___y_3238_ = v_a_3084_;
v___y_3239_ = v_a_3085_;
v___y_3240_ = v_a_3086_;
v___y_3241_ = v_a_3087_;
v___y_3242_ = v_a_3088_;
goto v___jp_3234_;
}
v___jp_3215_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3224_ = lean_box(v___x_3110_);
v___x_3225_ = lean_box(v___x_3105_);
lean_inc(v___x_3214_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 17, 8);
lean_closure_set(v___f_3226_, 0, v_a_3097_);
lean_closure_set(v___f_3226_, 1, v_rhs_3216_);
lean_closure_set(v___f_3226_, 2, v___x_3224_);
lean_closure_set(v___f_3226_, 3, v___x_3101_);
lean_closure_set(v___f_3226_, 4, v___x_3102_);
lean_closure_set(v___f_3226_, 5, v___x_3103_);
lean_closure_set(v___f_3226_, 6, v___x_3214_);
lean_closure_set(v___f_3226_, 7, v___x_3225_);
v___x_3227_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3227_, 0, v_dec_3081_);
v___x_3228_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3228_, 0, v_letOrReassign_3079_);
lean_closure_set(v___x_3228_, 1, v_a_3091_);
lean_closure_set(v___x_3228_, 2, v___x_3227_);
v___x_3229_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__9, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__9);
v___x_3230_ = l_Lean_MessageData_ofSyntax(v___x_3214_);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_box(0);
v___x_3233_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3231_, v___x_3228_, v___f_3226_, v___x_3232_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3233_;
}
v___jp_3234_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_unsigned_to_nat(4u);
v___x_3244_ = l_Lean_Syntax_getArg(v___x_3108_, v___x_3243_);
lean_dec(v___x_3108_);
if (lean_obj_tag(v_xType_x3f_3235_) == 0)
{
v_rhs_3216_ = v___x_3244_;
v___y_3217_ = v___y_3236_;
v___y_3218_ = v___y_3237_;
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3239_;
v___y_3221_ = v___y_3240_;
v___y_3222_ = v___y_3241_;
v___y_3223_ = v___y_3242_;
goto v___jp_3215_;
}
else
{
lean_object* v_val_3245_; lean_object* v_ref_3246_; lean_object* v_quotContext_3247_; lean_object* v_currMacroScope_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_val_3245_ = lean_ctor_get(v_xType_x3f_3235_, 0);
lean_inc(v_val_3245_);
lean_dec_ref(v_xType_x3f_3235_);
v_ref_3246_ = lean_ctor_get(v___y_3241_, 5);
v_quotContext_3247_ = lean_ctor_get(v___y_3241_, 10);
v_currMacroScope_3248_ = lean_ctor_get(v___y_3241_, 11);
v___x_3249_ = l_Lean_SourceInfo_fromRef(v_ref_3246_, v___x_3110_);
v___x_3250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3252_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3249_);
v___x_3253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3249_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3255_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3256_ = lean_box(0);
lean_inc(v_currMacroScope_3248_);
lean_inc(v_quotContext_3247_);
v___x_3257_ = l_Lean_addMacroScope(v_quotContext_3247_, v___x_3256_, v_currMacroScope_3248_);
v___x_3258_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
lean_inc(v___x_3249_);
v___x_3259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3249_);
lean_ctor_set(v___x_3259_, 1, v___x_3255_);
lean_ctor_set(v___x_3259_, 2, v___x_3257_);
lean_ctor_set(v___x_3259_, 3, v___x_3258_);
lean_inc(v___x_3249_);
v___x_3260_ = l_Lean_Syntax_node1(v___x_3249_, v___x_3254_, v___x_3259_);
lean_inc(v___x_3249_);
v___x_3261_ = l_Lean_Syntax_node2(v___x_3249_, v___x_3251_, v___x_3253_, v___x_3260_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_3249_);
v___x_3263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3249_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
lean_inc(v___x_3249_);
v___x_3265_ = l_Lean_Syntax_node1(v___x_3249_, v___x_3264_, v_val_3245_);
v___x_3266_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_3249_);
v___x_3267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3249_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = l_Lean_Syntax_node5(v___x_3249_, v___x_3250_, v___x_3261_, v___x_3244_, v___x_3263_, v___x_3265_, v___x_3267_);
v_rhs_3216_ = v___x_3268_;
v___y_3217_ = v___y_3236_;
v___y_3218_ = v___y_3237_;
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___y_3239_;
v___y_3221_ = v___y_3240_;
v___y_3222_ = v___y_3241_;
v___y_3223_ = v___y_3242_;
goto v___jp_3215_;
}
}
}
}
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_del_object(v___x_3099_);
lean_dec(v_a_3097_);
lean_dec(v_a_3091_);
v___x_3283_ = lean_box(v___x_3105_);
lean_inc(v___x_3108_);
v___x_3284_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3284_, 0, v___x_3108_);
lean_closure_set(v___x_3284_, 1, v___x_3283_);
lean_inc_ref(v_a_3087_);
v___x_3285_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v___x_3284_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v_ref_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v_ref_3287_ = lean_ctor_get(v_a_3087_, 5);
v___x_3288_ = 0;
v___x_3289_ = l_Lean_SourceInfo_fromRef(v_ref_3287_, v___x_3288_);
v___x_3290_ = l_Lean_Syntax_node1(v___x_3289_, v___x_3104_, v_a_3286_);
lean_inc(v___x_3290_);
v___x_3291_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 11, 3);
lean_closure_set(v___x_3291_, 0, v_letOrReassign_3079_);
lean_closure_set(v___x_3291_, 1, v___x_3290_);
lean_closure_set(v___x_3291_, 2, v_dec_3081_);
v___x_3292_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3108_, v___x_3290_, v___x_3291_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
return v___x_3292_;
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v___x_3108_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v_a_3293_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3285_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3285_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3094_);
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
return v___x_3096_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_letOrReassign_3079_);
v_a_3302_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3093_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3093_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_a_3091_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_decl_3080_);
lean_dec(v_letOrReassign_3079_);
v_a_3310_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3092_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3092_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec_ref(v_dec_3081_);
lean_dec(v_decl_3080_);
lean_dec(v_letOrReassign_3079_);
v_a_3318_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3090_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3090_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3327_, v_x_3328_, v_x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_cls_3331_, lean_object* v_msg_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_3331_, v_msg_3332_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_cls_3342_, lean_object* v_msg_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_cls_3342_, v_msg_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9(lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_3358_, v___y_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___boxed(lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9(v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec_ref(v___y_3362_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3371_, lean_object* v_beforeStx_3372_, lean_object* v_afterStx_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_beforeStx_3372_, v_afterStx_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_beforeStx_3385_, lean_object* v_afterStx_3386_, lean_object* v_x_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3384_, v_beforeStx_3385_, v_afterStx_3386_, v_x_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13(lean_object* v_00_u03b1_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v_x_3398_, v___y_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13(v_00_u03b1_3402_, v_x_3403_, v___y_3404_, v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v_x_3403_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18(lean_object* v_00_u03b1_3407_, lean_object* v_ref_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_ref_3408_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_ref_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18(v_00_u03b1_3418_, v_ref_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10(lean_object* v_00_u03b1_3429_, lean_object* v_x_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v_x_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_x_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10(v_00_u03b1_3440_, v_x_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3451_, lean_object* v_x_3452_, size_t v_x_3453_, size_t v_x_3454_, lean_object* v_x_3455_, lean_object* v_x_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3452_, v_x_3453_, v_x_3454_, v_x_3455_, v_x_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3458_, lean_object* v_x_3459_, lean_object* v_x_3460_, lean_object* v_x_3461_, lean_object* v_x_3462_, lean_object* v_x_3463_){
_start:
{
size_t v_x_78608__boxed_3464_; size_t v_x_78609__boxed_3465_; lean_object* v_res_3466_; 
v_x_78608__boxed_3464_ = lean_unbox_usize(v_x_3460_);
lean_dec(v_x_3460_);
v_x_78609__boxed_3465_ = lean_unbox_usize(v_x_3461_);
lean_dec(v_x_3461_);
v_res_3466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3458_, v_x_3459_, v_x_78608__boxed_3464_, v_x_78609__boxed_3465_, v_x_3462_, v_x_3463_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11(lean_object* v_00_u03b1_3467_, lean_object* v_stx_3468_, lean_object* v_output_3469_, lean_object* v_x_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_stx_3468_, v_output_3469_, v_x_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_stx_3480_, lean_object* v_output_3481_, lean_object* v_x_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11(v_00_u03b1_3479_, v_stx_3480_, v_output_3481_, v_x_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15(lean_object* v_as_3491_, lean_object* v_as_x27_3492_, lean_object* v_b_3493_, lean_object* v_a_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_as_x27_3492_, v_b_3493_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___boxed(lean_object* v_as_3504_, lean_object* v_as_x27_3505_, lean_object* v_b_3506_, lean_object* v_a_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15(v_as_3504_, v_as_x27_3505_, v_b_3506_, v_a_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v_as_3504_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17(lean_object* v_00_u03b1_3517_, lean_object* v_ref_3518_, lean_object* v_msg_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_ref_3518_, v_msg_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_ref_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17(v_00_u03b1_3529_, v_ref_3530_, v_msg_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_ref_3530_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3541_, lean_object* v_n_3542_, lean_object* v_k_3543_, lean_object* v_v_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_n_3542_, v_k_3543_, v_v_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_3546_, size_t v_depth_3547_, lean_object* v_keys_3548_, lean_object* v_vals_3549_, lean_object* v_heq_3550_, lean_object* v_i_3551_, lean_object* v_entries_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_depth_3547_, v_keys_3548_, v_vals_3549_, v_i_3551_, v_entries_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_3554_, lean_object* v_depth_3555_, lean_object* v_keys_3556_, lean_object* v_vals_3557_, lean_object* v_heq_3558_, lean_object* v_i_3559_, lean_object* v_entries_3560_){
_start:
{
size_t v_depth_boxed_3561_; lean_object* v_res_3562_; 
v_depth_boxed_3561_ = lean_unbox_usize(v_depth_3555_);
lean_dec(v_depth_3555_);
v_res_3562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6(v_00_u03b2_3554_, v_depth_boxed_3561_, v_keys_3556_, v_vals_3557_, v_heq_3558_, v_i_3559_, v_entries_3560_);
lean_dec_ref(v_vals_3557_);
lean_dec_ref(v_keys_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19(lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___boxed(lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19(v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14(lean_object* v_00_u03b1_3579_, lean_object* v_x_3580_, lean_object* v_mkInfoTree_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_3580_, v_mkInfoTree_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_x_3591_, lean_object* v_mkInfoTree_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14(v_00_u03b1_3590_, v_x_3591_, v_mkInfoTree_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23(lean_object* v_00_u03b1_3601_, lean_object* v_msg_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_3602_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b1_3612_, lean_object* v_msg_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23(v_00_u03b1_3612_, v_msg_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15(lean_object* v_00_u03b2_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(v_x_3624_, v_x_3625_, v_x_3626_, v_x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22(lean_object* v_00_u03b2_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v_x_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
uint8_t v_res_3636_; lean_object* v_r_3637_; 
v_res_3636_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22(v_00_u03b2_3633_, v_x_3634_, v_x_3635_);
lean_dec_ref(v_x_3635_);
v_r_3637_ = lean_box(v_res_3636_);
return v_r_3637_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26(lean_object* v_00_u03b2_3638_, lean_object* v_x_3639_, size_t v_x_3640_, lean_object* v_x_3641_){
_start:
{
uint8_t v___x_3642_; 
v___x_3642_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_3639_, v_x_3640_, v_x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___boxed(lean_object* v_00_u03b2_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_){
_start:
{
size_t v_x_78797__boxed_3647_; uint8_t v_res_3648_; lean_object* v_r_3649_; 
v_x_78797__boxed_3647_ = lean_unbox_usize(v_x_3645_);
lean_dec(v_x_3645_);
v_res_3648_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26(v_00_u03b2_3643_, v_x_3644_, v_x_78797__boxed_3647_, v_x_3646_);
lean_dec_ref(v_x_3646_);
v_r_3649_ = lean_box(v_res_3648_);
return v_r_3649_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29(lean_object* v_00_u03b2_3650_, lean_object* v_keys_3651_, lean_object* v_vals_3652_, lean_object* v_heq_3653_, lean_object* v_i_3654_, lean_object* v_k_3655_){
_start:
{
uint8_t v___x_3656_; 
v___x_3656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_keys_3651_, v_i_3654_, v_k_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___boxed(lean_object* v_00_u03b2_3657_, lean_object* v_keys_3658_, lean_object* v_vals_3659_, lean_object* v_heq_3660_, lean_object* v_i_3661_, lean_object* v_k_3662_){
_start:
{
uint8_t v_res_3663_; lean_object* v_r_3664_; 
v_res_3663_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29(v_00_u03b2_3657_, v_keys_3658_, v_vals_3659_, v_heq_3660_, v_i_3661_, v_k_3662_);
lean_dec_ref(v_k_3662_);
lean_dec_ref(v_vals_3659_);
lean_dec_ref(v_keys_3658_);
v_r_3664_ = lean_box(v_res_3663_);
return v_r_3664_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3668_ = l_Lean_stringToMessageData(v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3673_, lean_object* v_otherwise_x3f_3674_, uint8_t v___x_3675_, lean_object* v___x_3676_, lean_object* v___x_3677_, lean_object* v___x_3678_, lean_object* v___x_3679_, lean_object* v___x_3680_, lean_object* v_dec_3681_, uint8_t v___x_3682_, lean_object* v___y_3683_, lean_object* v___x_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; uint8_t v___y_3716_; 
switch(lean_obj_tag(v_letOrReassign_3673_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3674_) == 1)
{
lean_object* v_mutTk_x3f_3727_; lean_object* v_val_3728_; lean_object* v_ref_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3747_; 
v_mutTk_x3f_3727_ = lean_ctor_get(v_letOrReassign_3673_, 0);
v_val_3728_ = lean_ctor_get(v_otherwise_x3f_3674_, 0);
lean_inc(v_val_3728_);
lean_dec_ref(v_otherwise_x3f_3674_);
v_ref_3729_ = lean_ctor_get(v___y_3690_, 5);
v___x_3730_ = l_Lean_SourceInfo_fromRef(v_ref_3729_, v___x_3675_);
v___x_3731_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
v___x_3732_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3731_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3730_);
v___x_3734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3730_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3736_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3727_) == 1)
{
lean_object* v_val_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_val_3758_ = lean_ctor_get(v_mutTk_x3f_3727_, 0);
v___x_3759_ = l_Lean_SourceInfo_fromRef(v_val_3758_, v___x_3682_);
v___x_3760_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Array_mkArray1___redArg(v___x_3761_);
v___y_3747_ = v___x_3762_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_mk_empty_array_with_capacity(v___x_3684_);
v___y_3747_ = v___x_3763_;
goto v___jp_3746_;
}
v___jp_3737_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3742_ = l_Array_append___redArg(v___x_3736_, v___y_3741_);
lean_dec_ref(v___y_3741_);
lean_inc(v___x_3730_);
v___x_3743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3730_);
lean_ctor_set(v___x_3743_, 1, v___x_3735_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
v___x_3744_ = l_Lean_Syntax_node8(v___x_3730_, v___x_3732_, v___x_3734_, v___y_3738_, v___x_3679_, v___y_3740_, v___x_3680_, v___y_3739_, v_val_3728_, v___x_3743_);
v___x_3745_ = l_Lean_Elab_Do_elabDoElem(v___x_3744_, v_dec_3681_, v___x_3682_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3745_;
}
v___jp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3748_ = l_Array_append___redArg(v___x_3736_, v___y_3747_);
lean_dec_ref(v___y_3747_);
lean_inc(v___x_3730_);
v___x_3749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3730_);
lean_ctor_set(v___x_3749_, 1, v___x_3735_);
lean_ctor_set(v___x_3749_, 2, v___x_3748_);
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3730_);
v___x_3751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3730_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_3730_);
v___x_3753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3730_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
if (lean_obj_tag(v___y_3683_) == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3684_);
v___y_3738_ = v___x_3749_;
v___y_3739_ = v___x_3753_;
v___y_3740_ = v___x_3751_;
v___y_3741_ = v___x_3754_;
goto v___jp_3737_;
}
else
{
lean_object* v_val_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_val_3755_ = lean_ctor_get(v___y_3683_, 0);
lean_inc(v_val_3755_);
lean_dec_ref(v___y_3683_);
v___x_3756_ = lean_mk_empty_array_with_capacity(v___x_3684_);
v___x_3757_ = lean_array_push(v___x_3756_, v_val_3755_);
v___y_3738_ = v___x_3749_;
v___y_3739_ = v___x_3753_;
v___y_3740_ = v___x_3751_;
v___y_3741_ = v___x_3757_;
goto v___jp_3737_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3764_; lean_object* v_ref_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___y_3774_; 
lean_dec(v___y_3683_);
lean_dec(v_otherwise_x3f_3674_);
v_mutTk_x3f_3764_ = lean_ctor_get(v_letOrReassign_3673_, 0);
v_ref_3765_ = lean_ctor_get(v___y_3690_, 5);
v___x_3766_ = l_Lean_SourceInfo_fromRef(v_ref_3765_, v___x_3675_);
v___x_3767_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3676_);
v___x_3768_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3766_);
v___x_3770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3766_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3772_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3764_) == 1)
{
lean_object* v_val_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_val_3788_ = lean_ctor_get(v_mutTk_x3f_3764_, 0);
v___x_3789_ = l_Lean_SourceInfo_fromRef(v_val_3788_, v___x_3682_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Array_mkArray1___redArg(v___x_3791_);
v___y_3774_ = v___x_3792_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_mk_empty_array_with_capacity(v___x_3684_);
v___y_3774_ = v___x_3793_;
goto v___jp_3773_;
}
v___jp_3773_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3775_ = l_Array_append___redArg(v___x_3772_, v___y_3774_);
lean_dec_ref(v___y_3774_);
lean_inc(v___x_3766_);
v___x_3776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3766_);
lean_ctor_set(v___x_3776_, 1, v___x_3771_);
lean_ctor_set(v___x_3776_, 2, v___x_3775_);
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3676_);
v___x_3778_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3780_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3779_);
lean_inc(v___x_3766_);
v___x_3781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3766_);
lean_ctor_set(v___x_3781_, 1, v___x_3771_);
lean_ctor_set(v___x_3781_, 2, v___x_3772_);
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3766_);
v___x_3783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3766_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
lean_inc_ref(v___x_3781_);
lean_inc(v___x_3766_);
v___x_3784_ = l_Lean_Syntax_node5(v___x_3766_, v___x_3780_, v___x_3679_, v___x_3781_, v___x_3781_, v___x_3783_, v___x_3680_);
lean_inc(v___x_3766_);
v___x_3785_ = l_Lean_Syntax_node1(v___x_3766_, v___x_3778_, v___x_3784_);
v___x_3786_ = l_Lean_Syntax_node3(v___x_3766_, v___x_3768_, v___x_3770_, v___x_3776_, v___x_3785_);
v___x_3787_ = l_Lean_Elab_Do_elabDoElem(v___x_3786_, v_dec_3681_, v___x_3682_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3787_;
}
}
}
case 1:
{
lean_dec(v___y_3683_);
if (lean_obj_tag(v_otherwise_x3f_3674_) == 1)
{
lean_object* v___x_3794_; 
lean_dec_ref(v_otherwise_x3f_3674_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_dec_3681_);
lean_dec(v___x_3680_);
lean_dec(v___x_3679_);
lean_dec_ref(v___x_3678_);
lean_dec_ref(v___x_3677_);
lean_dec_ref(v___x_3676_);
v___x_3794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3794_;
}
else
{
lean_object* v_ref_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_dec(v_otherwise_x3f_3674_);
v_ref_3795_ = lean_ctor_get(v___y_3690_, 5);
v___x_3796_ = l_Lean_SourceInfo_fromRef(v_ref_3795_, v___x_3675_);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3676_);
v___x_3798_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3797_);
v___x_3799_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc(v___x_3796_);
v___x_3800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3796_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3676_);
v___x_3802_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3801_);
v___x_3803_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3804_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3803_);
v___x_3805_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3806_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3796_);
v___x_3807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3796_);
lean_ctor_set(v___x_3807_, 1, v___x_3805_);
lean_ctor_set(v___x_3807_, 2, v___x_3806_);
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3796_);
v___x_3809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3796_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
lean_inc_ref(v___x_3807_);
lean_inc(v___x_3796_);
v___x_3810_ = l_Lean_Syntax_node5(v___x_3796_, v___x_3804_, v___x_3679_, v___x_3807_, v___x_3807_, v___x_3809_, v___x_3680_);
lean_inc(v___x_3796_);
v___x_3811_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3802_, v___x_3810_);
v___x_3812_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3798_, v___x_3800_, v___x_3811_);
v___x_3813_ = l_Lean_Elab_Do_elabDoElem(v___x_3812_, v_dec_3681_, v___x_3682_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3813_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3674_);
if (lean_obj_tag(v___y_3683_) == 0)
{
v___y_3716_ = v___x_3682_;
goto v___jp_3715_;
}
else
{
lean_dec_ref(v___y_3683_);
v___y_3716_ = v___x_3675_;
goto v___jp_3715_;
}
}
}
v___jp_3693_:
{
lean_object* v_ref_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_ref_3701_ = lean_ctor_get(v___y_3699_, 5);
v___x_3702_ = l_Lean_SourceInfo_fromRef(v_ref_3701_, v___x_3675_);
v___x_3703_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3678_);
lean_inc_ref(v___x_3677_);
lean_inc_ref(v___x_3676_);
v___x_3704_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3703_);
v___x_3705_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3706_ = l_Lean_Name_mkStr4(v___x_3676_, v___x_3677_, v___x_3678_, v___x_3705_);
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3708_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3702_);
v___x_3709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3702_);
lean_ctor_set(v___x_3709_, 1, v___x_3707_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3702_);
v___x_3711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3702_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
lean_inc_ref(v___x_3709_);
lean_inc(v___x_3702_);
v___x_3712_ = l_Lean_Syntax_node5(v___x_3702_, v___x_3706_, v___x_3679_, v___x_3709_, v___x_3709_, v___x_3711_, v___x_3680_);
v___x_3713_ = l_Lean_Syntax_node1(v___x_3702_, v___x_3704_, v___x_3712_);
v___x_3714_ = l_Lean_Elab_Do_elabDoElem(v___x_3713_, v_dec_3681_, v___x_3682_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3714_;
}
v___jp_3715_:
{
if (v___y_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_dec_3681_);
lean_dec(v___x_3680_);
lean_dec(v___x_3679_);
lean_dec_ref(v___x_3678_);
lean_dec_ref(v___x_3677_);
lean_dec_ref(v___x_3676_);
v___x_3717_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3718_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v___x_3717_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
else
{
v___y_3694_ = v___y_3685_;
v___y_3695_ = v___y_3686_;
v___y_3696_ = v___y_3687_;
v___y_3697_ = v___y_3688_;
v___y_3698_ = v___y_3689_;
v___y_3699_ = v___y_3690_;
v___y_3700_ = v___y_3691_;
goto v___jp_3693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_3814_ = _args[0];
lean_object* v_otherwise_x3f_3815_ = _args[1];
lean_object* v___x_3816_ = _args[2];
lean_object* v___x_3817_ = _args[3];
lean_object* v___x_3818_ = _args[4];
lean_object* v___x_3819_ = _args[5];
lean_object* v___x_3820_ = _args[6];
lean_object* v___x_3821_ = _args[7];
lean_object* v_dec_3822_ = _args[8];
lean_object* v___x_3823_ = _args[9];
lean_object* v___y_3824_ = _args[10];
lean_object* v___x_3825_ = _args[11];
lean_object* v___y_3826_ = _args[12];
lean_object* v___y_3827_ = _args[13];
lean_object* v___y_3828_ = _args[14];
lean_object* v___y_3829_ = _args[15];
lean_object* v___y_3830_ = _args[16];
lean_object* v___y_3831_ = _args[17];
lean_object* v___y_3832_ = _args[18];
lean_object* v___y_3833_ = _args[19];
_start:
{
uint8_t v___x_37476__boxed_3834_; uint8_t v___x_37482__boxed_3835_; lean_object* v_res_3836_; 
v___x_37476__boxed_3834_ = lean_unbox(v___x_3816_);
v___x_37482__boxed_3835_ = lean_unbox(v___x_3823_);
v_res_3836_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_3814_, v_otherwise_x3f_3815_, v___x_37476__boxed_3834_, v___x_3817_, v___x_3818_, v___x_3819_, v___x_3820_, v___x_3821_, v_dec_3822_, v___x_37482__boxed_3835_, v___y_3824_, v___x_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___x_3825_);
lean_dec(v_letOrReassign_3814_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_3837_, lean_object* v_otherwise_x3f_3838_, uint8_t v___x_3839_, lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v___x_3842_, lean_object* v___x_3843_, lean_object* v___x_3844_, lean_object* v_dec_3845_, uint8_t v___x_3846_, lean_object* v___y_3847_, lean_object* v___x_3848_, uint8_t v___x_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3881_; 
switch(lean_obj_tag(v_letOrReassign_3837_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3838_) == 1)
{
lean_object* v_mutTk_x3f_3892_; lean_object* v_val_3893_; lean_object* v_ref_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3912_; 
v_mutTk_x3f_3892_ = lean_ctor_get(v_letOrReassign_3837_, 0);
v_val_3893_ = lean_ctor_get(v_otherwise_x3f_3838_, 0);
lean_inc(v_val_3893_);
lean_dec_ref(v_otherwise_x3f_3838_);
v_ref_3894_ = lean_ctor_get(v___y_3855_, 5);
v___x_3895_ = l_Lean_SourceInfo_fromRef(v_ref_3894_, v___x_3839_);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
v___x_3897_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3896_);
v___x_3898_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3895_);
v___x_3899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3895_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3901_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3892_) == 1)
{
lean_object* v_val_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_val_3923_ = lean_ctor_get(v_mutTk_x3f_3892_, 0);
v___x_3924_ = l_Lean_SourceInfo_fromRef(v_val_3923_, v___x_3846_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = l_Array_mkArray1___redArg(v___x_3926_);
v___y_3912_ = v___x_3927_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3912_ = v___x_3928_;
goto v___jp_3911_;
}
v___jp_3902_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3907_ = l_Array_append___redArg(v___x_3901_, v___y_3906_);
lean_dec_ref(v___y_3906_);
lean_inc(v___x_3895_);
v___x_3908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3895_);
lean_ctor_set(v___x_3908_, 1, v___x_3900_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
v___x_3909_ = l_Lean_Syntax_node8(v___x_3895_, v___x_3897_, v___x_3899_, v___y_3904_, v___x_3843_, v___y_3905_, v___x_3844_, v___y_3903_, v_val_3893_, v___x_3908_);
v___x_3910_ = l_Lean_Elab_Do_elabDoElem(v___x_3909_, v_dec_3845_, v___x_3846_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3910_;
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3913_ = l_Array_append___redArg(v___x_3901_, v___y_3912_);
lean_dec_ref(v___y_3912_);
lean_inc(v___x_3895_);
v___x_3914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3895_);
lean_ctor_set(v___x_3914_, 1, v___x_3900_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3895_);
v___x_3916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3895_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_3895_);
v___x_3918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3895_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
if (lean_obj_tag(v___y_3847_) == 0)
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3903_ = v___x_3918_;
v___y_3904_ = v___x_3914_;
v___y_3905_ = v___x_3916_;
v___y_3906_ = v___x_3919_;
goto v___jp_3902_;
}
else
{
lean_object* v_val_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_val_3920_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_val_3920_);
lean_dec_ref(v___y_3847_);
v___x_3921_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___x_3922_ = lean_array_push(v___x_3921_, v_val_3920_);
v___y_3903_ = v___x_3918_;
v___y_3904_ = v___x_3914_;
v___y_3905_ = v___x_3916_;
v___y_3906_ = v___x_3922_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3929_; lean_object* v_ref_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___y_3939_; 
lean_dec(v___y_3847_);
lean_dec(v_otherwise_x3f_3838_);
v_mutTk_x3f_3929_ = lean_ctor_get(v_letOrReassign_3837_, 0);
v_ref_3930_ = lean_ctor_get(v___y_3855_, 5);
v___x_3931_ = l_Lean_SourceInfo_fromRef(v_ref_3930_, v___x_3839_);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3933_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3931_);
v___x_3935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3931_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3937_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3929_) == 1)
{
lean_object* v_val_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_val_3953_ = lean_ctor_get(v_mutTk_x3f_3929_, 0);
v___x_3954_ = l_Lean_SourceInfo_fromRef(v_val_3953_, v___x_3846_);
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = l_Array_mkArray1___redArg(v___x_3956_);
v___y_3939_ = v___x_3957_;
goto v___jp_3938_;
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3939_ = v___x_3958_;
goto v___jp_3938_;
}
v___jp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3940_ = l_Array_append___redArg(v___x_3937_, v___y_3939_);
lean_dec_ref(v___y_3939_);
lean_inc(v___x_3931_);
v___x_3941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3931_);
lean_ctor_set(v___x_3941_, 1, v___x_3936_);
lean_ctor_set(v___x_3941_, 2, v___x_3940_);
v___x_3942_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3943_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3942_);
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3945_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3944_);
lean_inc(v___x_3931_);
v___x_3946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3931_);
lean_ctor_set(v___x_3946_, 1, v___x_3936_);
lean_ctor_set(v___x_3946_, 2, v___x_3937_);
v___x_3947_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3931_);
v___x_3948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3931_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
lean_inc_ref(v___x_3946_);
lean_inc(v___x_3931_);
v___x_3949_ = l_Lean_Syntax_node5(v___x_3931_, v___x_3945_, v___x_3843_, v___x_3946_, v___x_3946_, v___x_3948_, v___x_3844_);
lean_inc(v___x_3931_);
v___x_3950_ = l_Lean_Syntax_node1(v___x_3931_, v___x_3943_, v___x_3949_);
v___x_3951_ = l_Lean_Syntax_node3(v___x_3931_, v___x_3933_, v___x_3935_, v___x_3941_, v___x_3950_);
v___x_3952_ = l_Lean_Elab_Do_elabDoElem(v___x_3951_, v_dec_3845_, v___x_3846_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3952_;
}
}
}
case 1:
{
lean_dec(v___y_3847_);
if (lean_obj_tag(v_otherwise_x3f_3838_) == 1)
{
lean_object* v___x_3959_; 
lean_dec_ref(v_otherwise_x3f_3838_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec_ref(v_dec_3845_);
lean_dec(v___x_3844_);
lean_dec(v___x_3843_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v___x_3840_);
v___x_3959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3959_;
}
else
{
lean_object* v_ref_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec(v_otherwise_x3f_3838_);
v_ref_3960_ = lean_ctor_get(v___y_3855_, 5);
v___x_3961_ = l_Lean_SourceInfo_fromRef(v_ref_3960_, v___x_3839_);
v___x_3962_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3963_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3962_);
v___x_3964_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc(v___x_3961_);
v___x_3965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3961_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3967_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3966_);
v___x_3968_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3969_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3968_);
v___x_3970_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3971_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3961_);
v___x_3972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3961_);
lean_ctor_set(v___x_3972_, 1, v___x_3970_);
lean_ctor_set(v___x_3972_, 2, v___x_3971_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3961_);
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3961_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
lean_inc_ref(v___x_3972_);
lean_inc(v___x_3961_);
v___x_3975_ = l_Lean_Syntax_node5(v___x_3961_, v___x_3969_, v___x_3843_, v___x_3972_, v___x_3972_, v___x_3974_, v___x_3844_);
lean_inc(v___x_3961_);
v___x_3976_ = l_Lean_Syntax_node1(v___x_3961_, v___x_3967_, v___x_3975_);
v___x_3977_ = l_Lean_Syntax_node2(v___x_3961_, v___x_3963_, v___x_3965_, v___x_3976_);
v___x_3978_ = l_Lean_Elab_Do_elabDoElem(v___x_3977_, v_dec_3845_, v___x_3846_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3978_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3838_);
if (lean_obj_tag(v___y_3847_) == 0)
{
v___y_3881_ = v___x_3849_;
goto v___jp_3880_;
}
else
{
lean_dec_ref(v___y_3847_);
v___y_3881_ = v___x_3839_;
goto v___jp_3880_;
}
}
}
v___jp_3858_:
{
lean_object* v_ref_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_ref_3866_ = lean_ctor_get(v___y_3864_, 5);
v___x_3867_ = l_Lean_SourceInfo_fromRef(v_ref_3866_, v___x_3839_);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3869_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3868_);
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3871_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3870_);
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3873_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3867_);
v___x_3874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3867_);
lean_ctor_set(v___x_3874_, 1, v___x_3872_);
lean_ctor_set(v___x_3874_, 2, v___x_3873_);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3867_);
v___x_3876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3867_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
lean_inc_ref(v___x_3874_);
lean_inc(v___x_3867_);
v___x_3877_ = l_Lean_Syntax_node5(v___x_3867_, v___x_3871_, v___x_3843_, v___x_3874_, v___x_3874_, v___x_3876_, v___x_3844_);
v___x_3878_ = l_Lean_Syntax_node1(v___x_3867_, v___x_3869_, v___x_3877_);
v___x_3879_ = l_Lean_Elab_Do_elabDoElem(v___x_3878_, v_dec_3845_, v___x_3846_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3879_;
}
v___jp_3880_:
{
if (v___y_3881_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec_ref(v_dec_3845_);
lean_dec(v___x_3844_);
lean_dec(v___x_3843_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v___x_3840_);
v___x_3882_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3883_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v___x_3882_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
else
{
v___y_3859_ = v___y_3850_;
v___y_3860_ = v___y_3851_;
v___y_3861_ = v___y_3852_;
v___y_3862_ = v___y_3853_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
goto v___jp_3858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_3979_ = _args[0];
lean_object* v_otherwise_x3f_3980_ = _args[1];
lean_object* v___x_3981_ = _args[2];
lean_object* v___x_3982_ = _args[3];
lean_object* v___x_3983_ = _args[4];
lean_object* v___x_3984_ = _args[5];
lean_object* v___x_3985_ = _args[6];
lean_object* v___x_3986_ = _args[7];
lean_object* v_dec_3987_ = _args[8];
lean_object* v___x_3988_ = _args[9];
lean_object* v___y_3989_ = _args[10];
lean_object* v___x_3990_ = _args[11];
lean_object* v___x_3991_ = _args[12];
lean_object* v___y_3992_ = _args[13];
lean_object* v___y_3993_ = _args[14];
lean_object* v___y_3994_ = _args[15];
lean_object* v___y_3995_ = _args[16];
lean_object* v___y_3996_ = _args[17];
lean_object* v___y_3997_ = _args[18];
lean_object* v___y_3998_ = _args[19];
lean_object* v___y_3999_ = _args[20];
_start:
{
uint8_t v___x_37810__boxed_4000_; uint8_t v___x_37816__boxed_4001_; uint8_t v___x_37819__boxed_4002_; lean_object* v_res_4003_; 
v___x_37810__boxed_4000_ = lean_unbox(v___x_3981_);
v___x_37816__boxed_4001_ = lean_unbox(v___x_3988_);
v___x_37819__boxed_4002_ = lean_unbox(v___x_3991_);
v_res_4003_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_3979_, v_otherwise_x3f_3980_, v___x_37810__boxed_4000_, v___x_3982_, v___x_3983_, v___x_3984_, v___x_3985_, v___x_3986_, v_dec_3987_, v___x_37816__boxed_4001_, v___y_3989_, v___x_3990_, v___x_37819__boxed_4002_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___x_3990_);
lean_dec(v_letOrReassign_3979_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4024_, lean_object* v_stx_4025_, lean_object* v_dec_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; 
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4037_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4025_);
v___x_4039_ = l_Lean_Syntax_isOfKind(v_stx_4025_, v___x_4038_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4040_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4025_);
v___x_4041_ = l_Lean_Syntax_isOfKind(v_stx_4025_, v___x_4040_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; 
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4042_;
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; 
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4043_);
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4044_);
v___x_4046_ = l_Lean_Syntax_isOfKind(v___x_4044_, v___x_4045_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4132_; lean_object* v_patType_x3f_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v___x_4132_ = lean_unsigned_to_nat(1u);
v___x_4163_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4132_);
v___x_4164_ = l_Lean_Syntax_isNone(v___x_4163_);
if (v___x_4164_ == 0)
{
uint8_t v___x_4165_; 
lean_inc(v___x_4163_);
v___x_4165_ = l_Lean_Syntax_matchesNull(v___x_4163_, v___x_4132_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec(v___x_4163_);
lean_dec(v___x_4044_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4166_;
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4167_ = l_Lean_Syntax_getArg(v___x_4163_, v___x_4043_);
lean_dec(v___x_4163_);
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4167_);
v___x_4169_ = l_Lean_Syntax_isOfKind(v___x_4167_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; 
lean_dec(v___x_4167_);
lean_dec(v___x_4044_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4170_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4170_;
}
else
{
lean_object* v_patType_x3f_4171_; lean_object* v___x_4172_; 
v_patType_x3f_4171_ = l_Lean_Syntax_getArg(v___x_4167_, v___x_4132_);
lean_dec(v___x_4167_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_patType_x3f_4171_);
v_patType_x3f_4134_ = v___x_4172_;
v___y_4135_ = v_a_4027_;
v___y_4136_ = v_a_4028_;
v___y_4137_ = v_a_4029_;
v___y_4138_ = v_a_4030_;
v___y_4139_ = v_a_4031_;
v___y_4140_ = v_a_4032_;
v___y_4141_ = v_a_4033_;
goto v___jp_4133_;
}
}
}
else
{
lean_object* v___x_4173_; 
lean_dec(v___x_4163_);
v___x_4173_ = lean_box(0);
v_patType_x3f_4134_ = v___x_4173_;
v___y_4135_ = v_a_4027_;
v___y_4136_ = v_a_4028_;
v___y_4137_ = v_a_4029_;
v___y_4138_ = v_a_4030_;
v___y_4139_ = v_a_4031_;
v___y_4140_ = v_a_4032_;
v___y_4141_ = v_a_4033_;
goto v___jp_4133_;
}
v___jp_4133_:
{
lean_object* v___x_4142_; lean_object* v_rhs_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v___x_4142_ = lean_unsigned_to_nat(3u);
v_rhs_4143_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4142_);
v___x_4144_ = lean_unsigned_to_nat(4u);
v___x_4145_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4144_);
lean_dec(v_stx_4025_);
v___x_4146_ = l_Lean_Syntax_isNone(v___x_4145_);
if (v___x_4146_ == 0)
{
uint8_t v___x_4147_; 
lean_inc(v___x_4145_);
v___x_4147_ = l_Lean_Syntax_matchesNull(v___x_4145_, v___x_4142_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_dec(v___x_4145_);
lean_dec(v_rhs_4143_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v_patType_x3f_4134_);
lean_dec(v___x_4044_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_letOrReassign_4024_);
v___x_4148_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4148_;
}
else
{
lean_object* v___x_4149_; lean_object* v_otherwise_x3f_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4150_ = l_Lean_Syntax_getArg(v___x_4145_, v___x_4132_);
v___x_4151_ = l_Lean_Syntax_getArg(v___x_4145_, v___x_4149_);
lean_dec(v___x_4145_);
v___x_4152_ = l_Lean_Syntax_getOptional_x3f(v___x_4151_);
lean_dec(v___x_4151_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4153_; 
v___x_4153_ = lean_box(0);
v___y_4077_ = v___y_4140_;
v___y_4078_ = v___y_4136_;
v___y_4079_ = v___y_4139_;
v___y_4080_ = v___y_4137_;
v___y_4081_ = v_otherwise_x3f_4150_;
v___y_4082_ = v_rhs_4143_;
v___y_4083_ = v_patType_x3f_4134_;
v___y_4084_ = v___y_4138_;
v___y_4085_ = v___y_4141_;
v___y_4086_ = v___y_4135_;
v___y_4087_ = v___x_4153_;
goto v___jp_4076_;
}
else
{
lean_object* v_val_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
v_val_4154_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4152_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_val_4154_);
lean_dec(v___x_4152_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_val_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
v___y_4077_ = v___y_4140_;
v___y_4078_ = v___y_4136_;
v___y_4079_ = v___y_4139_;
v___y_4080_ = v___y_4137_;
v___y_4081_ = v_otherwise_x3f_4150_;
v___y_4082_ = v_rhs_4143_;
v___y_4083_ = v_patType_x3f_4134_;
v___y_4084_ = v___y_4138_;
v___y_4085_ = v___y_4141_;
v___y_4086_ = v___y_4135_;
v___y_4087_ = v___x_4159_;
goto v___jp_4076_;
}
}
}
}
}
else
{
lean_object* v___x_4162_; 
lean_dec(v___x_4145_);
v___x_4162_ = lean_box(0);
v___y_4048_ = v_patType_x3f_4134_;
v___y_4049_ = v___y_4140_;
v___y_4050_ = v___y_4138_;
v___y_4051_ = v___x_4162_;
v___y_4052_ = v___y_4141_;
v___y_4053_ = v___y_4136_;
v___y_4054_ = v_rhs_4143_;
v___y_4055_ = v___y_4139_;
v___y_4056_ = v___y_4137_;
v___y_4057_ = v___y_4135_;
v___y_4058_ = v___x_4162_;
goto v___jp_4047_;
}
}
}
else
{
lean_object* v_pattern_4174_; lean_object* v___x_4175_; lean_object* v_patType_x3f_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___x_4222_; uint8_t v___x_4223_; 
v_pattern_4174_ = l_Lean_Syntax_getArg(v___x_4044_, v___x_4043_);
v___x_4175_ = lean_unsigned_to_nat(1u);
v___x_4222_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4175_);
v___x_4223_ = l_Lean_Syntax_isNone(v___x_4222_);
if (v___x_4223_ == 0)
{
uint8_t v___x_4224_; 
lean_inc(v___x_4222_);
v___x_4224_ = l_Lean_Syntax_matchesNull(v___x_4222_, v___x_4175_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; 
lean_dec(v___x_4222_);
lean_dec(v_pattern_4174_);
lean_dec(v___x_4044_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4225_;
}
else
{
lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v___x_4226_ = l_Lean_Syntax_getArg(v___x_4222_, v___x_4043_);
lean_dec(v___x_4222_);
v___x_4227_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4226_);
v___x_4228_ = l_Lean_Syntax_isOfKind(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; 
lean_dec(v___x_4226_);
lean_dec(v_pattern_4174_);
lean_dec(v___x_4044_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4229_;
}
else
{
lean_object* v_patType_x3f_4230_; lean_object* v___x_4231_; 
v_patType_x3f_4230_ = l_Lean_Syntax_getArg(v___x_4226_, v___x_4175_);
lean_dec(v___x_4226_);
v___x_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4231_, 0, v_patType_x3f_4230_);
v_patType_x3f_4177_ = v___x_4231_;
v___y_4178_ = v_a_4027_;
v___y_4179_ = v_a_4028_;
v___y_4180_ = v_a_4029_;
v___y_4181_ = v_a_4030_;
v___y_4182_ = v_a_4031_;
v___y_4183_ = v_a_4032_;
v___y_4184_ = v_a_4033_;
goto v___jp_4176_;
}
}
}
else
{
lean_object* v___x_4232_; 
lean_dec(v___x_4222_);
v___x_4232_ = lean_box(0);
v_patType_x3f_4177_ = v___x_4232_;
v___y_4178_ = v_a_4027_;
v___y_4179_ = v_a_4028_;
v___y_4180_ = v_a_4029_;
v___y_4181_ = v_a_4030_;
v___y_4182_ = v_a_4031_;
v___y_4183_ = v_a_4032_;
v___y_4184_ = v_a_4033_;
goto v___jp_4176_;
}
v___jp_4176_:
{
lean_object* v___x_4185_; lean_object* v_rhs_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4185_ = lean_unsigned_to_nat(3u);
v_rhs_4186_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4185_);
v___x_4187_ = lean_unsigned_to_nat(4u);
v___x_4188_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4187_);
lean_dec(v_stx_4025_);
lean_inc(v___x_4188_);
v___x_4189_ = l_Lean_Syntax_matchesNull(v___x_4188_, v___x_4043_);
if (v___x_4189_ == 0)
{
uint8_t v___x_4190_; 
lean_dec(v_pattern_4174_);
v___x_4190_ = l_Lean_Syntax_isNone(v___x_4188_);
if (v___x_4190_ == 0)
{
uint8_t v___x_4191_; 
lean_inc(v___x_4188_);
v___x_4191_ = l_Lean_Syntax_matchesNull(v___x_4188_, v___x_4185_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
lean_dec(v___x_4188_);
lean_dec(v_rhs_4186_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v_patType_x3f_4177_);
lean_dec(v___x_4044_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_letOrReassign_4024_);
v___x_4192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4192_;
}
else
{
lean_object* v___x_4193_; lean_object* v_otherwise_x3f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4194_ = l_Lean_Syntax_getArg(v___x_4188_, v___x_4175_);
v___x_4195_ = l_Lean_Syntax_getArg(v___x_4188_, v___x_4193_);
lean_dec(v___x_4188_);
v___x_4196_ = l_Lean_Syntax_getOptional_x3f(v___x_4195_);
lean_dec(v___x_4195_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_box(0);
v___y_4120_ = v___y_4184_;
v___y_4121_ = v___y_4182_;
v___y_4122_ = v___y_4178_;
v___y_4123_ = v_patType_x3f_4177_;
v___y_4124_ = v___y_4179_;
v___y_4125_ = v_rhs_4186_;
v___y_4126_ = v_otherwise_x3f_4194_;
v___y_4127_ = v___y_4180_;
v___y_4128_ = v___y_4181_;
v___y_4129_ = v___y_4183_;
v___y_4130_ = v___x_4197_;
goto v___jp_4119_;
}
else
{
lean_object* v_val_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_val_4198_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4196_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_val_4198_);
lean_dec(v___x_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_val_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
v___y_4120_ = v___y_4184_;
v___y_4121_ = v___y_4182_;
v___y_4122_ = v___y_4178_;
v___y_4123_ = v_patType_x3f_4177_;
v___y_4124_ = v___y_4179_;
v___y_4125_ = v_rhs_4186_;
v___y_4126_ = v_otherwise_x3f_4194_;
v___y_4127_ = v___y_4180_;
v___y_4128_ = v___y_4181_;
v___y_4129_ = v___y_4183_;
v___y_4130_ = v___x_4203_;
goto v___jp_4119_;
}
}
}
}
}
else
{
lean_object* v___x_4206_; 
lean_dec(v___x_4188_);
v___x_4206_ = lean_box(0);
v___y_4090_ = v___y_4182_;
v___y_4091_ = v_rhs_4186_;
v___y_4092_ = v___x_4206_;
v___y_4093_ = v___y_4181_;
v___y_4094_ = v_patType_x3f_4177_;
v___y_4095_ = v___y_4183_;
v___y_4096_ = v___y_4179_;
v___y_4097_ = v___y_4178_;
v___y_4098_ = v___y_4184_;
v___y_4099_ = v___y_4180_;
v___y_4100_ = v___x_4206_;
goto v___jp_4089_;
}
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec(v___x_4188_);
lean_dec(v___x_4044_);
lean_dec(v_letOrReassign_4024_);
v___x_4207_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
lean_inc(v___y_4184_);
lean_inc_ref(v___y_4183_);
v___x_4208_ = l_Lean_Core_mkFreshUserName(v___x_4207_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; uint8_t v_kind_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref(v___x_4208_);
v_kind_4210_ = lean_ctor_get_uint8(v_dec_4026_, sizeof(void*)*3);
v___x_4211_ = l_Lean_mkIdentFrom(v_pattern_4174_, v_a_4209_, v___x_4039_);
lean_dec(v_pattern_4174_);
v___x_4212_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4212_, 0, v_dec_4026_);
v___x_4213_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4211_, v_patType_x3f_4177_, v_rhs_4186_, v___x_4212_, v_kind_4210_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4213_;
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v_rhs_4186_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v_patType_x3f_4177_);
lean_dec(v_pattern_4174_);
lean_dec_ref(v_dec_4026_);
v_a_4214_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4208_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4208_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
}
v___jp_4047_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
lean_inc(v___y_4052_);
lean_inc_ref(v___y_4049_);
v___x_4060_ = l_Lean_Core_mkFreshUserName(v___x_4059_, v___y_4049_, v___y_4052_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___y_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref(v___x_4060_);
v___x_4062_ = l_Lean_mkIdentFrom(v___x_4044_, v_a_4061_, v___x_4046_);
v___x_4063_ = lean_box(v___x_4046_);
v___x_4064_ = lean_box(v___x_4041_);
lean_inc(v___x_4062_);
v___y_4065_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4065_, 0, v_letOrReassign_4024_);
lean_closure_set(v___y_4065_, 1, v___y_4051_);
lean_closure_set(v___y_4065_, 2, v___x_4063_);
lean_closure_set(v___y_4065_, 3, v___x_4035_);
lean_closure_set(v___y_4065_, 4, v___x_4036_);
lean_closure_set(v___y_4065_, 5, v___x_4037_);
lean_closure_set(v___y_4065_, 6, v___x_4044_);
lean_closure_set(v___y_4065_, 7, v___x_4062_);
lean_closure_set(v___y_4065_, 8, v_dec_4026_);
lean_closure_set(v___y_4065_, 9, v___x_4064_);
lean_closure_set(v___y_4065_, 10, v___y_4058_);
lean_closure_set(v___y_4065_, 11, v___x_4043_);
v___x_4066_ = 0;
v___x_4067_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4062_, v___y_4048_, v___y_4054_, v___y_4065_, v___x_4066_, v___y_4057_, v___y_4053_, v___y_4056_, v___y_4050_, v___y_4055_, v___y_4049_, v___y_4052_);
return v___x_4067_;
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v___x_4044_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_letOrReassign_4024_);
v_a_4068_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4060_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4060_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
v___jp_4076_:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___y_4081_);
v___y_4048_ = v___y_4083_;
v___y_4049_ = v___y_4077_;
v___y_4050_ = v___y_4084_;
v___y_4051_ = v___x_4088_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4078_;
v___y_4054_ = v___y_4082_;
v___y_4055_ = v___y_4079_;
v___y_4056_ = v___y_4080_;
v___y_4057_ = v___y_4086_;
v___y_4058_ = v___y_4087_;
goto v___jp_4047_;
}
v___jp_4089_:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
lean_inc(v___y_4098_);
lean_inc_ref(v___y_4095_);
v___x_4102_ = l_Lean_Core_mkFreshUserName(v___x_4101_, v___y_4095_, v___y_4098_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___y_4108_; uint8_t v___x_4109_; lean_object* v___x_4110_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref(v___x_4102_);
v___x_4104_ = l_Lean_mkIdentFrom(v___x_4044_, v_a_4103_, v___x_4039_);
v___x_4105_ = lean_box(v___x_4039_);
v___x_4106_ = lean_box(v___x_4041_);
v___x_4107_ = lean_box(v___x_4046_);
lean_inc(v___x_4104_);
v___y_4108_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4108_, 0, v_letOrReassign_4024_);
lean_closure_set(v___y_4108_, 1, v___y_4092_);
lean_closure_set(v___y_4108_, 2, v___x_4105_);
lean_closure_set(v___y_4108_, 3, v___x_4035_);
lean_closure_set(v___y_4108_, 4, v___x_4036_);
lean_closure_set(v___y_4108_, 5, v___x_4037_);
lean_closure_set(v___y_4108_, 6, v___x_4044_);
lean_closure_set(v___y_4108_, 7, v___x_4104_);
lean_closure_set(v___y_4108_, 8, v_dec_4026_);
lean_closure_set(v___y_4108_, 9, v___x_4106_);
lean_closure_set(v___y_4108_, 10, v___y_4100_);
lean_closure_set(v___y_4108_, 11, v___x_4043_);
lean_closure_set(v___y_4108_, 12, v___x_4107_);
v___x_4109_ = 0;
v___x_4110_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4104_, v___y_4094_, v___y_4091_, v___y_4108_, v___x_4109_, v___y_4097_, v___y_4096_, v___y_4099_, v___y_4093_, v___y_4090_, v___y_4095_, v___y_4098_);
return v___x_4110_;
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v___x_4044_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_letOrReassign_4024_);
v_a_4111_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4102_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4102_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4119_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___y_4126_);
v___y_4090_ = v___y_4121_;
v___y_4091_ = v___y_4125_;
v___y_4092_ = v___x_4131_;
v___y_4093_ = v___y_4128_;
v___y_4094_ = v___y_4123_;
v___y_4095_ = v___y_4129_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4122_;
v___y_4098_ = v___y_4120_;
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4130_;
goto v___jp_4089_;
}
}
}
else
{
lean_object* v___x_4233_; lean_object* v_x_4234_; lean_object* v___y_4236_; lean_object* v_xType_x3f_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v_xType_x3f_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4233_ = lean_unsigned_to_nat(0u);
v_x_4234_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4233_);
v___x_4296_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4234_);
v___x_4297_ = l_Lean_Syntax_isOfKind(v_x_4234_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; 
lean_dec(v_x_4234_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4298_;
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4299_ = lean_unsigned_to_nat(1u);
v___x_4300_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4299_);
v___x_4301_ = l_Lean_Syntax_isNone(v___x_4300_);
if (v___x_4301_ == 0)
{
uint8_t v___x_4302_; 
lean_inc(v___x_4300_);
v___x_4302_ = l_Lean_Syntax_matchesNull(v___x_4300_, v___x_4299_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec(v___x_4300_);
lean_dec(v_x_4234_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4303_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4304_ = l_Lean_Syntax_getArg(v___x_4300_, v___x_4233_);
lean_dec(v___x_4300_);
v___x_4305_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4304_);
v___x_4306_ = l_Lean_Syntax_isOfKind(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
lean_dec(v___x_4304_);
lean_dec(v_x_4234_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v___x_4307_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4307_;
}
else
{
lean_object* v_xType_x3f_4308_; lean_object* v___x_4309_; 
v_xType_x3f_4308_ = l_Lean_Syntax_getArg(v___x_4304_, v___x_4299_);
lean_dec(v___x_4304_);
v___x_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_xType_x3f_4308_);
v_xType_x3f_4251_ = v___x_4309_;
v___y_4252_ = v_a_4027_;
v___y_4253_ = v_a_4028_;
v___y_4254_ = v_a_4029_;
v___y_4255_ = v_a_4030_;
v___y_4256_ = v_a_4031_;
v___y_4257_ = v_a_4032_;
v___y_4258_ = v_a_4033_;
goto v___jp_4250_;
}
}
}
else
{
lean_object* v___x_4310_; 
lean_dec(v___x_4300_);
v___x_4310_ = lean_box(0);
v_xType_x3f_4251_ = v___x_4310_;
v___y_4252_ = v_a_4027_;
v___y_4253_ = v_a_4028_;
v___y_4254_ = v_a_4029_;
v___y_4255_ = v_a_4030_;
v___y_4256_ = v_a_4031_;
v___y_4257_ = v_a_4032_;
v___y_4258_ = v_a_4033_;
goto v___jp_4250_;
}
}
v___jp_4235_:
{
uint8_t v_kind_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_kind_4245_ = lean_ctor_get_uint8(v_dec_4026_, sizeof(void*)*3);
v___x_4246_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4024_);
lean_dec(v_letOrReassign_4024_);
v___x_4247_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4247_, 0, v_dec_4026_);
lean_inc(v_x_4234_);
v___x_4248_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4248_, 0, lean_box(0));
lean_closure_set(v___x_4248_, 1, v___x_4246_);
lean_closure_set(v___x_4248_, 2, v_x_4234_);
lean_closure_set(v___x_4248_, 3, v___x_4247_);
v___x_4249_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4234_, v_xType_x3f_4237_, v___y_4236_, v___x_4248_, v_kind_4245_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
return v___x_4249_;
}
v___jp_4250_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4259_ = lean_unsigned_to_nat(1u);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4259_);
lean_inc(v_x_4234_);
v___x_4261_ = lean_array_push(v___x_4260_, v_x_4234_);
lean_inc_ref(v___y_4257_);
v___x_4262_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4024_, v___x_4261_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec_ref(v___x_4261_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v___x_4263_; lean_object* v_rhs_4264_; 
lean_dec_ref(v___x_4262_);
v___x_4263_ = lean_unsigned_to_nat(3u);
v_rhs_4264_ = l_Lean_Syntax_getArg(v_stx_4025_, v___x_4263_);
lean_dec(v_stx_4025_);
if (lean_obj_tag(v_letOrReassign_4024_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4251_) == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = l_Lean_TSyntax_getId(v_x_4234_);
v___x_4266_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4265_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref(v___x_4266_);
v___x_4268_ = l_Lean_LocalDecl_type(v_a_4267_);
lean_dec(v_a_4267_);
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
v___x_4269_ = l_Lean_Elab_Term_exprToSyntax(v___x_4268_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4271_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_a_4270_);
v___y_4236_ = v_rhs_4264_;
v_xType_x3f_4237_ = v___x_4271_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
v___y_4242_ = v___y_4256_;
v___y_4243_ = v___y_4257_;
v___y_4244_ = v___y_4258_;
goto v___jp_4235_;
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_rhs_4264_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v_x_4234_);
lean_dec_ref(v_dec_4026_);
v_a_4272_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4269_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4269_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_rhs_4264_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v_x_4234_);
lean_dec_ref(v_dec_4026_);
v_a_4280_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4266_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4266_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
else
{
v___y_4236_ = v_rhs_4264_;
v_xType_x3f_4237_ = v_xType_x3f_4251_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
v___y_4242_ = v___y_4256_;
v___y_4243_ = v___y_4257_;
v___y_4244_ = v___y_4258_;
goto v___jp_4235_;
}
}
else
{
v___y_4236_ = v_rhs_4264_;
v_xType_x3f_4237_ = v_xType_x3f_4251_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
v___y_4242_ = v___y_4256_;
v___y_4243_ = v___y_4257_;
v___y_4244_ = v___y_4258_;
goto v___jp_4235_;
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v_xType_x3f_4251_);
lean_dec(v_x_4234_);
lean_dec_ref(v_dec_4026_);
lean_dec(v_stx_4025_);
lean_dec(v_letOrReassign_4024_);
v_a_4288_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4262_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4262_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4311_, lean_object* v_stx_4312_, lean_object* v_dec_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4311_, v_stx_4312_, v_dec_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4328_, lean_object* v_dec_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_mutTk_x3f_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4354_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4328_);
v___x_4355_ = l_Lean_Syntax_isOfKind(v_stx_4328_, v___x_4354_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; 
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec_ref(v_dec_4329_);
lean_dec(v_stx_4328_);
v___x_4356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = l_Lean_Syntax_getArg(v_stx_4328_, v___x_4357_);
v___x_4359_ = l_Lean_Syntax_isNone(v___x_4358_);
if (v___x_4359_ == 0)
{
uint8_t v___x_4360_; 
lean_inc(v___x_4358_);
v___x_4360_ = l_Lean_Syntax_matchesNull(v___x_4358_, v___x_4357_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; 
lean_dec(v___x_4358_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec_ref(v_dec_4329_);
lean_dec(v_stx_4328_);
v___x_4361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4361_;
}
else
{
lean_object* v___x_4362_; lean_object* v_mutTk_x3f_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_4363_ = l_Lean_Syntax_getArg(v___x_4358_, v___x_4362_);
lean_dec(v___x_4358_);
v___x_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4364_, 0, v_mutTk_x3f_4363_);
v_mutTk_x3f_4339_ = v___x_4364_;
v___y_4340_ = v_a_4330_;
v___y_4341_ = v_a_4331_;
v___y_4342_ = v_a_4332_;
v___y_4343_ = v_a_4333_;
v___y_4344_ = v_a_4334_;
v___y_4345_ = v_a_4335_;
v___y_4346_ = v_a_4336_;
goto v___jp_4338_;
}
}
else
{
lean_object* v___x_4365_; 
lean_dec(v___x_4358_);
v___x_4365_ = lean_box(0);
v_mutTk_x3f_4339_ = v___x_4365_;
v___y_4340_ = v_a_4330_;
v___y_4341_ = v_a_4331_;
v___y_4342_ = v_a_4332_;
v___y_4343_ = v_a_4333_;
v___y_4344_ = v_a_4334_;
v___y_4345_ = v_a_4335_;
v___y_4346_ = v_a_4336_;
goto v___jp_4338_;
}
}
v___jp_4338_:
{
lean_object* v___x_4347_; lean_object* v_decl_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4347_ = lean_unsigned_to_nat(2u);
v_decl_4348_ = l_Lean_Syntax_getArg(v_stx_4328_, v___x_4347_);
lean_dec(v_stx_4328_);
v___x_4349_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4348_);
v___x_4350_ = l_Lean_Syntax_isOfKind(v_decl_4348_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
lean_dec(v_decl_4348_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v_mutTk_x3f_4339_);
lean_dec_ref(v_dec_4329_);
v___x_4351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4351_;
}
else
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v_mutTk_x3f_4339_);
v___x_4353_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4352_, v_decl_4348_, v_dec_4329_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
return v___x_4353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4366_, lean_object* v_dec_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_Lean_Elab_Do_elabDoLet(v_stx_4366_, v_dec_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4384_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4387_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4388_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4384_, v___x_4385_, v___x_4386_, v___x_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4396_, lean_object* v_dec_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4406_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4396_);
v___x_4407_ = l_Lean_Syntax_isOfKind(v_stx_4396_, v___x_4406_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_a_4398_);
lean_dec_ref(v_dec_4397_);
lean_dec(v_stx_4396_);
v___x_4408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4408_;
}
else
{
lean_object* v___x_4409_; lean_object* v_decl_4410_; lean_object* v___x_4411_; uint8_t v___x_4412_; 
v___x_4409_ = lean_unsigned_to_nat(1u);
v_decl_4410_ = l_Lean_Syntax_getArg(v_stx_4396_, v___x_4409_);
lean_dec(v_stx_4396_);
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4410_);
v___x_4412_ = l_Lean_Syntax_isOfKind(v_decl_4410_, v___x_4411_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; 
lean_dec(v_decl_4410_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_a_4398_);
lean_dec_ref(v_dec_4397_);
v___x_4413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4413_;
}
else
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = lean_box(1);
v___x_4415_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4414_, v_decl_4410_, v_dec_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
return v___x_4415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4416_, lean_object* v_dec_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Elab_Do_elabDoHave(v_stx_4416_, v_dec_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4434_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4435_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4436_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4437_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4438_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4434_, v___x_4435_, v___x_4436_, v___x_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4443_, lean_object* v___x_4444_, lean_object* v___x_4445_, lean_object* v___x_4446_, lean_object* v_decls_4447_, lean_object* v_a_4448_, uint8_t v___x_4449_, lean_object* v_body_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_ref_4459_; uint8_t v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v_ref_4459_ = lean_ctor_get(v___y_4456_, 5);
v___x_4460_ = 0;
v___x_4461_ = l_Lean_SourceInfo_fromRef(v_ref_4459_, v___x_4460_);
v___x_4462_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4463_ = l_Lean_Name_mkStr4(v___x_4443_, v___x_4444_, v___x_4445_, v___x_4462_);
v___x_4464_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4461_);
v___x_4465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4461_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___x_4466_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
lean_inc(v___x_4461_);
v___x_4467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4461_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
lean_inc(v___x_4461_);
v___x_4468_ = l_Lean_Syntax_node2(v___x_4461_, v___x_4446_, v___x_4465_, v___x_4467_);
v___x_4469_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4461_);
v___x_4470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4461_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = l_Lean_Syntax_node4(v___x_4461_, v___x_4463_, v___x_4468_, v_decls_4447_, v___x_4470_, v_body_4450_);
v___x_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4472_, 0, v_a_4448_);
v___x_4473_ = l_Lean_Elab_Term_elabTerm(v___x_4471_, v___x_4472_, v___x_4449_, v___x_4449_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4474_, lean_object* v___x_4475_, lean_object* v___x_4476_, lean_object* v___x_4477_, lean_object* v_decls_4478_, lean_object* v_a_4479_, lean_object* v___x_4480_, lean_object* v_body_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
uint8_t v___x_4796__boxed_4490_; lean_object* v_res_4491_; 
v___x_4796__boxed_4490_ = lean_unbox(v___x_4480_);
v_res_4491_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4474_, v___x_4475_, v___x_4476_, v___x_4477_, v_decls_4478_, v_a_4479_, v___x_4796__boxed_4490_, v_body_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec_ref(v___y_4482_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
if (lean_obj_tag(v_a_4492_) == 0)
{
lean_object* v___x_4494_; 
v___x_4494_ = l_List_reverse___redArg(v_a_4493_);
return v___x_4494_;
}
else
{
lean_object* v_head_4495_; lean_object* v_tail_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4505_; 
v_head_4495_ = lean_ctor_get(v_a_4492_, 0);
v_tail_4496_ = lean_ctor_get(v_a_4492_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_a_4492_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4498_ = v_a_4492_;
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_tail_4496_);
lean_inc(v_head_4495_);
lean_dec(v_a_4492_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4500_ = l_Lean_MessageData_ofSyntax(v_head_4495_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 1, v_a_4493_);
lean_ctor_set(v___x_4498_, 0, v___x_4500_);
v___x_4502_ = v___x_4498_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_a_4493_);
v___x_4502_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
v_a_4492_ = v_tail_4496_;
v_a_4493_ = v___x_4502_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4523_ = l_Lean_stringToMessageData(v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4524_, lean_object* v_dec_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4534_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4535_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4536_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4524_);
v___x_4538_ = l_Lean_Syntax_isOfKind(v_stx_4524_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; 
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec_ref(v_dec_4525_);
lean_dec(v_stx_4524_);
v___x_4539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4539_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = l_Lean_Syntax_getArg(v_stx_4524_, v___x_4540_);
v___x_4542_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
v___x_4543_ = l_Lean_Syntax_isOfKind(v___x_4541_, v___x_4542_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec_ref(v_dec_4525_);
lean_dec(v_stx_4524_);
v___x_4544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v_decls_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4545_ = lean_unsigned_to_nat(1u);
v_decls_4546_ = l_Lean_Syntax_getArg(v_stx_4524_, v___x_4545_);
lean_dec(v_stx_4524_);
v___x_4547_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4546_);
v___x_4548_ = l_Lean_Syntax_isOfKind(v_decls_4546_, v___x_4547_);
if (v___x_4548_ == 0)
{
lean_object* v___x_4549_; 
lean_dec(v_decls_4546_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec_ref(v_dec_4525_);
v___x_4549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4549_;
}
else
{
lean_object* v___x_4550_; 
lean_inc(v_a_4532_);
lean_inc_ref(v_a_4531_);
lean_inc(v_a_4530_);
lean_inc_ref(v_a_4529_);
lean_inc(v_a_4528_);
lean_inc_ref(v_a_4527_);
lean_inc(v_decls_4546_);
v___x_4550_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4546_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v_doBlockResultType_4552_; lean_object* v___x_4553_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref(v___x_4550_);
v_doBlockResultType_4552_ = lean_ctor_get(v_a_4526_, 3);
lean_inc_ref(v_a_4526_);
lean_inc_ref(v_doBlockResultType_4552_);
v___x_4553_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_4552_, v_a_4526_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___f_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = lean_box(v___x_4548_);
v___f_4556_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4556_, 0, v___x_4534_);
lean_closure_set(v___f_4556_, 1, v___x_4535_);
lean_closure_set(v___f_4556_, 2, v___x_4536_);
lean_closure_set(v___f_4556_, 3, v___x_4542_);
lean_closure_set(v___f_4556_, 4, v_decls_4546_);
lean_closure_set(v___f_4556_, 5, v_a_4554_);
lean_closure_set(v___f_4556_, 6, v___x_4555_);
v___x_4557_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4558_ = lean_array_to_list(v_a_4551_);
v___x_4559_ = lean_box(0);
v___x_4560_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4558_, v___x_4559_);
v___x_4561_ = l_Lean_MessageData_ofList(v___x_4560_);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4557_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4563_, 0, v_dec_4525_);
v___x_4564_ = lean_box(0);
v___x_4565_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4562_, v___x_4563_, v___f_4556_, v___x_4564_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4565_;
}
else
{
lean_dec(v_a_4551_);
lean_dec(v_decls_4546_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec_ref(v_dec_4525_);
return v___x_4553_;
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec(v_decls_4546_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec_ref(v_dec_4525_);
v_a_4566_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4550_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4550_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4574_, lean_object* v_dec_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4574_, v_dec_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4592_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4593_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4594_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4595_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4596_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4592_, v___x_4593_, v___x_4594_, v___x_4595_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4612_, lean_object* v_dec_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___x_4651_; uint8_t v___x_4652_; 
v___x_4651_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4612_);
v___x_4652_ = l_Lean_Syntax_isOfKind(v_stx_4612_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
lean_dec(v_stx_4612_);
v___x_4653_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4653_;
}
else
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4654_ = lean_unsigned_to_nat(0u);
v___x_4655_ = l_Lean_Syntax_getArg(v_stx_4612_, v___x_4654_);
lean_dec(v_stx_4612_);
v___x_4656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_4655_);
v___x_4657_ = l_Lean_Syntax_isOfKind(v___x_4655_, v___x_4656_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4658_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_4655_);
v___x_4659_ = l_Lean_Syntax_isOfKind(v___x_4655_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; 
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v_decl_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4662_ = lean_unsigned_to_nat(1u);
v___x_4663_ = lean_mk_empty_array_with_capacity(v___x_4662_);
v___x_4664_ = lean_array_push(v___x_4663_, v___x_4655_);
v___x_4665_ = lean_box(2);
v_decl_4666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_4666_, 0, v___x_4665_);
lean_ctor_set(v_decl_4666_, 1, v___x_4661_);
lean_ctor_set(v_decl_4666_, 2, v___x_4664_);
v___x_4667_ = lean_box(2);
v___x_4668_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4667_, v_decl_4666_, v_dec_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
return v___x_4668_;
}
}
else
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = l_Lean_Syntax_getArg(v___x_4655_, v___x_4654_);
v___x_4670_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4669_);
v___x_4671_ = l_Lean_Syntax_isOfKind(v___x_4669_, v___x_4670_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_dec(v___x_4669_);
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4672_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4672_;
}
else
{
lean_object* v___x_4673_; lean_object* v_xType_x3f_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___x_4700_; uint8_t v___x_4701_; 
v___x_4673_ = l_Lean_Syntax_getArg(v___x_4669_, v___x_4654_);
lean_dec(v___x_4669_);
v___x_4700_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4673_);
v___x_4701_ = l_Lean_Syntax_isOfKind(v___x_4673_, v___x_4700_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; 
lean_dec(v___x_4673_);
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4702_;
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; 
v___x_4703_ = lean_unsigned_to_nat(1u);
v___x_4704_ = l_Lean_Syntax_getArg(v___x_4655_, v___x_4703_);
v___x_4705_ = l_Lean_Syntax_matchesNull(v___x_4704_, v___x_4654_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; 
lean_dec(v___x_4673_);
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4706_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4706_;
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4707_ = lean_unsigned_to_nat(2u);
v___x_4708_ = l_Lean_Syntax_getArg(v___x_4655_, v___x_4707_);
v___x_4709_ = l_Lean_Syntax_isNone(v___x_4708_);
if (v___x_4709_ == 0)
{
uint8_t v___x_4710_; 
lean_inc(v___x_4708_);
v___x_4710_ = l_Lean_Syntax_matchesNull(v___x_4708_, v___x_4703_);
if (v___x_4710_ == 0)
{
lean_object* v___x_4711_; 
lean_dec(v___x_4708_);
lean_dec(v___x_4673_);
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4711_;
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v___x_4712_ = l_Lean_Syntax_getArg(v___x_4708_, v___x_4654_);
lean_dec(v___x_4708_);
v___x_4713_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4712_);
v___x_4714_ = l_Lean_Syntax_isOfKind(v___x_4712_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; 
lean_dec(v___x_4712_);
lean_dec(v___x_4673_);
lean_dec(v___x_4655_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_dec_4613_);
v___x_4715_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4715_;
}
else
{
lean_object* v_xType_x3f_4716_; lean_object* v___x_4717_; 
v_xType_x3f_4716_ = l_Lean_Syntax_getArg(v___x_4712_, v___x_4703_);
lean_dec(v___x_4712_);
v___x_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4717_, 0, v_xType_x3f_4716_);
v_xType_x3f_4675_ = v___x_4717_;
v___y_4676_ = v_a_4614_;
v___y_4677_ = v_a_4615_;
v___y_4678_ = v_a_4616_;
v___y_4679_ = v_a_4617_;
v___y_4680_ = v_a_4618_;
v___y_4681_ = v_a_4619_;
v___y_4682_ = v_a_4620_;
goto v___jp_4674_;
}
}
}
else
{
lean_object* v___x_4718_; 
lean_dec(v___x_4708_);
v___x_4718_ = lean_box(0);
v_xType_x3f_4675_ = v___x_4718_;
v___y_4676_ = v_a_4614_;
v___y_4677_ = v_a_4615_;
v___y_4678_ = v_a_4616_;
v___y_4679_ = v_a_4617_;
v___y_4680_ = v_a_4618_;
v___y_4681_ = v_a_4619_;
v___y_4682_ = v_a_4620_;
goto v___jp_4674_;
}
}
}
v___jp_4674_:
{
lean_object* v_ref_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_ref_4683_ = lean_ctor_get(v___y_4681_, 5);
v___x_4684_ = lean_unsigned_to_nat(4u);
v___x_4685_ = l_Lean_Syntax_getArg(v___x_4655_, v___x_4684_);
lean_dec(v___x_4655_);
v___x_4686_ = 0;
v___x_4687_ = l_Lean_SourceInfo_fromRef(v_ref_4683_, v___x_4686_);
v___x_4688_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_4687_);
v___x_4689_ = l_Lean_Syntax_node1(v___x_4687_, v___x_4670_, v___x_4673_);
v___x_4690_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4691_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4687_);
v___x_4692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4687_);
lean_ctor_set(v___x_4692_, 1, v___x_4690_);
lean_ctor_set(v___x_4692_, 2, v___x_4691_);
if (lean_obj_tag(v_xType_x3f_4675_) == 1)
{
lean_object* v_val_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v_val_4693_ = lean_ctor_get(v_xType_x3f_4675_, 0);
lean_inc(v_val_4693_);
lean_dec_ref(v_xType_x3f_4675_);
v___x_4694_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4695_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_4687_);
v___x_4696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4687_);
lean_ctor_set(v___x_4696_, 1, v___x_4695_);
lean_inc(v___x_4687_);
v___x_4697_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4694_, v___x_4696_, v_val_4693_);
v___x_4698_ = l_Array_mkArray1___redArg(v___x_4697_);
v___y_4623_ = v___y_4678_;
v___y_4624_ = v___y_4681_;
v___y_4625_ = v___x_4692_;
v___y_4626_ = v___x_4685_;
v___y_4627_ = v___x_4687_;
v___y_4628_ = v___y_4676_;
v___y_4629_ = v___x_4689_;
v___y_4630_ = v___y_4682_;
v___y_4631_ = v___y_4677_;
v___y_4632_ = v___x_4691_;
v___y_4633_ = v___x_4690_;
v___y_4634_ = v___x_4688_;
v___y_4635_ = v___y_4679_;
v___y_4636_ = v___y_4680_;
v___y_4637_ = v___x_4698_;
goto v___jp_4622_;
}
else
{
lean_object* v___x_4699_; 
lean_dec(v_xType_x3f_4675_);
v___x_4699_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4623_ = v___y_4678_;
v___y_4624_ = v___y_4681_;
v___y_4625_ = v___x_4692_;
v___y_4626_ = v___x_4685_;
v___y_4627_ = v___x_4687_;
v___y_4628_ = v___y_4676_;
v___y_4629_ = v___x_4689_;
v___y_4630_ = v___y_4682_;
v___y_4631_ = v___y_4677_;
v___y_4632_ = v___x_4691_;
v___y_4633_ = v___x_4690_;
v___y_4634_ = v___x_4688_;
v___y_4635_ = v___y_4679_;
v___y_4636_ = v___y_4680_;
v___y_4637_ = v___x_4699_;
goto v___jp_4622_;
}
}
}
}
}
v___jp_4622_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4638_ = l_Array_append___redArg(v___y_4632_, v___y_4637_);
lean_dec_ref(v___y_4637_);
lean_inc(v___y_4627_);
v___x_4639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4639_, 0, v___y_4627_);
lean_ctor_set(v___x_4639_, 1, v___y_4633_);
lean_ctor_set(v___x_4639_, 2, v___x_4638_);
v___x_4640_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___y_4627_);
v___x_4641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4641_, 0, v___y_4627_);
lean_ctor_set(v___x_4641_, 1, v___x_4640_);
v___x_4642_ = l_Lean_Syntax_node5(v___y_4627_, v___y_4634_, v___y_4629_, v___y_4625_, v___x_4639_, v___x_4641_, v___y_4626_);
v___x_4643_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4644_ = lean_unsigned_to_nat(1u);
v___x_4645_ = lean_mk_empty_array_with_capacity(v___x_4644_);
v___x_4646_ = lean_array_push(v___x_4645_, v___x_4642_);
v___x_4647_ = lean_box(2);
v___x_4648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v___x_4643_);
lean_ctor_set(v___x_4648_, 2, v___x_4646_);
v___x_4649_ = lean_box(2);
v___x_4650_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4649_, v___x_4648_, v_dec_4613_, v___y_4628_, v___y_4631_, v___y_4623_, v___y_4635_, v___y_4636_, v___y_4624_, v___y_4630_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_4719_, lean_object* v_dec_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_Elab_Do_elabDoReassign(v_stx_4719_, v_dec_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4737_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4738_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_4739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_4740_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_4741_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4737_, v___x_4738_, v___x_4739_, v___x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_4763_, size_t v_sz_4764_, size_t v_i_4765_, lean_object* v_b_4766_, lean_object* v___y_4767_){
_start:
{
uint8_t v___x_4769_; 
v___x_4769_ = lean_usize_dec_lt(v_i_4765_, v_sz_4764_);
if (v___x_4769_ == 0)
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_b_4766_);
return v___x_4770_;
}
else
{
lean_object* v_ref_4771_; lean_object* v___x_4772_; lean_object* v_a_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; size_t v___x_4806_; size_t v___x_4807_; 
v_ref_4771_ = lean_ctor_get(v___y_4767_, 5);
v___x_4772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4773_ = lean_array_uget_borrowed(v_as_4763_, v_i_4765_);
v___x_4774_ = 0;
v___x_4775_ = l_Lean_SourceInfo_fromRef(v_ref_4771_, v___x_4774_);
v___x_4776_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4778_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4779_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4775_);
v___x_4780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4775_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc(v___x_4775_);
v___x_4782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4775_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
lean_inc(v___x_4775_);
v___x_4783_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4776_, v___x_4782_);
v___x_4784_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4785_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4786_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v_a_4773_);
lean_inc(v___x_4775_);
v___x_4787_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4786_, v_a_4773_);
v___x_4788_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4775_);
v___x_4789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4775_);
lean_ctor_set(v___x_4789_, 1, v___x_4776_);
lean_ctor_set(v___x_4789_, 2, v___x_4788_);
v___x_4790_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_4775_);
v___x_4791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4775_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
lean_inc(v_a_4773_);
lean_inc_ref_n(v___x_4789_, 2);
lean_inc(v___x_4775_);
v___x_4792_ = l_Lean_Syntax_node5(v___x_4775_, v___x_4785_, v___x_4787_, v___x_4789_, v___x_4789_, v___x_4791_, v_a_4773_);
lean_inc(v___x_4775_);
v___x_4793_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4784_, v___x_4792_);
lean_inc(v___x_4775_);
v___x_4794_ = l_Lean_Syntax_node3(v___x_4775_, v___x_4778_, v___x_4780_, v___x_4783_, v___x_4793_);
v___x_4795_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4775_);
v___x_4796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4775_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
lean_inc(v___x_4775_);
v___x_4797_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4776_, v___x_4796_);
lean_inc(v___x_4775_);
v___x_4798_ = l_Lean_Syntax_node2(v___x_4775_, v___x_4777_, v___x_4794_, v___x_4797_);
v___x_4799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
lean_inc(v___x_4775_);
v___x_4801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4775_);
lean_ctor_set(v___x_4801_, 1, v___x_4800_);
lean_inc(v___x_4775_);
v___x_4802_ = l_Lean_Syntax_node2(v___x_4775_, v___x_4799_, v___x_4801_, v_b_4766_);
lean_inc(v___x_4775_);
v___x_4803_ = l_Lean_Syntax_node2(v___x_4775_, v___x_4777_, v___x_4802_, v___x_4789_);
lean_inc(v___x_4775_);
v___x_4804_ = l_Lean_Syntax_node2(v___x_4775_, v___x_4776_, v___x_4798_, v___x_4803_);
v___x_4805_ = l_Lean_Syntax_node1(v___x_4775_, v___x_4772_, v___x_4804_);
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4765_, v___x_4806_);
v_i_4765_ = v___x_4807_;
v_b_4766_ = v___x_4805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_4809_, lean_object* v_sz_4810_, lean_object* v_i_4811_, lean_object* v_b_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
size_t v_sz_boxed_4815_; size_t v_i_boxed_4816_; lean_object* v_res_4817_; 
v_sz_boxed_4815_ = lean_unbox_usize(v_sz_4810_);
lean_dec(v_sz_4810_);
v_i_boxed_4816_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_res_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4809_, v_sz_boxed_4815_, v_i_boxed_4816_, v_b_4812_, v___y_4813_);
lean_dec_ref(v___y_4813_);
lean_dec_ref(v_as_4809_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_4818_, size_t v_sz_4819_, size_t v_i_4820_, lean_object* v_b_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
uint8_t v___x_4830_; 
v___x_4830_ = lean_usize_dec_lt(v_i_4820_, v_sz_4819_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v_b_4821_);
return v___x_4831_;
}
else
{
lean_object* v_ref_4832_; lean_object* v___x_4833_; lean_object* v_a_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; size_t v___x_4867_; size_t v___x_4868_; lean_object* v___x_4869_; 
v_ref_4832_ = lean_ctor_get(v___y_4827_, 5);
v___x_4833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4834_ = lean_array_uget_borrowed(v_as_4818_, v_i_4820_);
v___x_4835_ = 0;
v___x_4836_ = l_Lean_SourceInfo_fromRef(v_ref_4832_, v___x_4835_);
v___x_4837_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4839_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4840_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4836_);
v___x_4841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4836_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
v___x_4842_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc(v___x_4836_);
v___x_4843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4836_);
lean_ctor_set(v___x_4843_, 1, v___x_4842_);
lean_inc(v___x_4836_);
v___x_4844_ = l_Lean_Syntax_node1(v___x_4836_, v___x_4837_, v___x_4843_);
v___x_4845_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4846_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4847_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v_a_4834_);
lean_inc(v___x_4836_);
v___x_4848_ = l_Lean_Syntax_node1(v___x_4836_, v___x_4847_, v_a_4834_);
v___x_4849_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4836_);
v___x_4850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4836_);
lean_ctor_set(v___x_4850_, 1, v___x_4837_);
lean_ctor_set(v___x_4850_, 2, v___x_4849_);
v___x_4851_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_4836_);
v___x_4852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4836_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
lean_inc(v_a_4834_);
lean_inc_ref_n(v___x_4850_, 2);
lean_inc(v___x_4836_);
v___x_4853_ = l_Lean_Syntax_node5(v___x_4836_, v___x_4846_, v___x_4848_, v___x_4850_, v___x_4850_, v___x_4852_, v_a_4834_);
lean_inc(v___x_4836_);
v___x_4854_ = l_Lean_Syntax_node1(v___x_4836_, v___x_4845_, v___x_4853_);
lean_inc(v___x_4836_);
v___x_4855_ = l_Lean_Syntax_node3(v___x_4836_, v___x_4839_, v___x_4841_, v___x_4844_, v___x_4854_);
v___x_4856_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4836_);
v___x_4857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4836_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
lean_inc(v___x_4836_);
v___x_4858_ = l_Lean_Syntax_node1(v___x_4836_, v___x_4837_, v___x_4857_);
lean_inc(v___x_4836_);
v___x_4859_ = l_Lean_Syntax_node2(v___x_4836_, v___x_4838_, v___x_4855_, v___x_4858_);
v___x_4860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
lean_inc(v___x_4836_);
v___x_4862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4836_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
lean_inc(v___x_4836_);
v___x_4863_ = l_Lean_Syntax_node2(v___x_4836_, v___x_4860_, v___x_4862_, v_b_4821_);
lean_inc(v___x_4836_);
v___x_4864_ = l_Lean_Syntax_node2(v___x_4836_, v___x_4838_, v___x_4863_, v___x_4850_);
lean_inc(v___x_4836_);
v___x_4865_ = l_Lean_Syntax_node2(v___x_4836_, v___x_4837_, v___x_4859_, v___x_4864_);
v___x_4866_ = l_Lean_Syntax_node1(v___x_4836_, v___x_4833_, v___x_4865_);
v___x_4867_ = ((size_t)1ULL);
v___x_4868_ = lean_usize_add(v_i_4820_, v___x_4867_);
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4818_, v_sz_4819_, v___x_4868_, v___x_4866_, v___y_4827_);
return v___x_4869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_4870_, lean_object* v_sz_4871_, lean_object* v_i_4872_, lean_object* v_b_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
size_t v_sz_boxed_4882_; size_t v_i_boxed_4883_; lean_object* v_res_4884_; 
v_sz_boxed_4882_ = lean_unbox_usize(v_sz_4871_);
lean_dec(v_sz_4871_);
v_i_boxed_4883_ = lean_unbox_usize(v_i_4872_);
lean_dec(v_i_4872_);
v_res_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_4870_, v_sz_boxed_4882_, v_i_boxed_4883_, v_b_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec_ref(v_as_4870_);
return v_res_4884_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_4925_ = l_String_toRawSubstring_x27(v___x_4924_);
return v___x_4925_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_4940_ = l_String_toRawSubstring_x27(v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_4957_, lean_object* v_dec_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v___x_4967_; uint8_t v___x_4968_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v_body_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; lean_object* v___y_5027_; lean_object* v_a_5028_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v_mutTk_x3f_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; 
v___x_4967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_4957_);
v___x_4968_ = l_Lean_Syntax_isOfKind(v_stx_4957_, v___x_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_5130_; 
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec_ref(v_dec_4958_);
lean_dec(v_stx_4957_);
v___x_5130_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5130_;
}
else
{
lean_object* v___x_5131_; lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5131_ = lean_unsigned_to_nat(1u);
v___x_5132_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_5131_);
v___x_5133_ = l_Lean_Syntax_isNone(v___x_5132_);
if (v___x_5133_ == 0)
{
uint8_t v___x_5134_; 
lean_inc(v___x_5132_);
v___x_5134_ = l_Lean_Syntax_matchesNull(v___x_5132_, v___x_5131_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; 
lean_dec(v___x_5132_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec_ref(v_dec_4958_);
lean_dec(v_stx_4957_);
v___x_5135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5135_;
}
else
{
lean_object* v___x_5136_; lean_object* v_mutTk_x3f_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5137_ = l_Lean_Syntax_getArg(v___x_5132_, v___x_5136_);
lean_dec(v___x_5132_);
v___x_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5138_, 0, v_mutTk_x3f_5137_);
v_mutTk_x3f_5104_ = v___x_5138_;
v___y_5105_ = v_a_4959_;
v___y_5106_ = v_a_4960_;
v___y_5107_ = v_a_4961_;
v___y_5108_ = v_a_4962_;
v___y_5109_ = v_a_4963_;
v___y_5110_ = v_a_4964_;
v___y_5111_ = v_a_4965_;
goto v___jp_5103_;
}
}
else
{
lean_object* v___x_5139_; 
lean_dec(v___x_5132_);
v___x_5139_ = lean_box(0);
v_mutTk_x3f_5104_ = v___x_5139_;
v___y_5105_ = v_a_4959_;
v___y_5106_ = v_a_4960_;
v___y_5107_ = v_a_4961_;
v___y_5108_ = v_a_4962_;
v___y_5109_ = v_a_4963_;
v___y_5110_ = v_a_4964_;
v___y_5111_ = v_a_4965_;
goto v___jp_5103_;
}
}
v___jp_4969_:
{
lean_object* v_ref_4981_; uint8_t v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v_ref_4981_ = lean_ctor_get(v___y_4979_, 5);
v___x_4982_ = 0;
v___x_4983_ = l_Lean_SourceInfo_fromRef(v_ref_4981_, v___x_4982_);
v___x_4984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_4985_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
lean_inc(v___x_4983_);
v___x_4986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4983_);
lean_ctor_set(v___x_4986_, 1, v___x_4985_);
v___x_4987_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4988_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4983_);
v___x_4989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4983_);
lean_ctor_set(v___x_4989_, 1, v___x_4987_);
lean_ctor_set(v___x_4989_, 2, v___x_4988_);
v___x_4990_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref(v___x_4989_);
lean_inc(v___x_4983_);
v___x_4991_ = l_Lean_Syntax_node2(v___x_4983_, v___x_4990_, v___x_4989_, v___y_4971_);
lean_inc(v___x_4983_);
v___x_4992_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4987_, v___x_4991_);
v___x_4993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
lean_inc(v___x_4983_);
v___x_4994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4983_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_4996_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_4997_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_4983_);
v___x_4998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4983_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
lean_inc(v___x_4983_);
v___x_4999_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4987_, v___y_4972_);
lean_inc(v___x_4983_);
v___x_5000_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4987_, v___x_4999_);
v___x_5001_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
lean_inc(v___x_4983_);
v___x_5002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4983_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
lean_inc_ref(v___x_5002_);
lean_inc_ref(v___x_4998_);
lean_inc(v___x_4983_);
v___x_5003_ = l_Lean_Syntax_node4(v___x_4983_, v___x_4996_, v___x_4998_, v___x_5000_, v___x_5002_, v_body_4973_);
v___x_5004_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5005_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
lean_inc(v___x_4983_);
v___x_5006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_4983_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
lean_inc(v___x_4983_);
v___x_5007_ = l_Lean_Syntax_node1(v___x_4983_, v___x_5004_, v___x_5006_);
lean_inc(v___x_4983_);
v___x_5008_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4987_, v___x_5007_);
lean_inc(v___x_4983_);
v___x_5009_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4987_, v___x_5008_);
lean_inc(v___x_4983_);
v___x_5010_ = l_Lean_Syntax_node4(v___x_4983_, v___x_4996_, v___x_4998_, v___x_5009_, v___x_5002_, v___y_4970_);
lean_inc(v___x_4983_);
v___x_5011_ = l_Lean_Syntax_node2(v___x_4983_, v___x_4987_, v___x_5003_, v___x_5010_);
lean_inc(v___x_4983_);
v___x_5012_ = l_Lean_Syntax_node1(v___x_4983_, v___x_4995_, v___x_5011_);
lean_inc_ref_n(v___x_4989_, 2);
v___x_5013_ = l_Lean_Syntax_node7(v___x_4983_, v___x_4984_, v___x_4986_, v___x_4989_, v___x_4989_, v___x_4989_, v___x_4992_, v___x_4994_, v___x_5012_);
v___x_5014_ = l_Lean_Elab_Do_elabDoElem(v___x_5013_, v_dec_4958_, v___x_4968_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
return v___x_5014_;
}
v___jp_5015_:
{
if (lean_obj_tag(v___y_5017_) == 0)
{
lean_dec_ref(v___y_5024_);
v___y_4970_ = v___y_5018_;
v___y_4971_ = v___y_5023_;
v___y_4972_ = v___y_5025_;
v_body_4973_ = v_a_5028_;
v___y_4974_ = v___y_5027_;
v___y_4975_ = v___y_5020_;
v___y_4976_ = v___y_5021_;
v___y_4977_ = v___y_5022_;
v___y_4978_ = v___y_5026_;
v___y_4979_ = v___y_5016_;
v___y_4980_ = v___y_5019_;
goto v___jp_4969_;
}
else
{
lean_dec_ref(v___y_5017_);
if (v___x_4968_ == 0)
{
lean_dec_ref(v___y_5024_);
v___y_4970_ = v___y_5018_;
v___y_4971_ = v___y_5023_;
v___y_4972_ = v___y_5025_;
v_body_4973_ = v_a_5028_;
v___y_4974_ = v___y_5027_;
v___y_4975_ = v___y_5020_;
v___y_4976_ = v___y_5021_;
v___y_4977_ = v___y_5022_;
v___y_4978_ = v___y_5026_;
v___y_4979_ = v___y_5016_;
v___y_4980_ = v___y_5019_;
goto v___jp_4969_;
}
else
{
size_t v_sz_5029_; size_t v___x_5030_; lean_object* v___x_5031_; 
v_sz_5029_ = lean_array_size(v___y_5024_);
v___x_5030_ = ((size_t)0ULL);
v___x_5031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5024_, v_sz_5029_, v___x_5030_, v_a_5028_, v___y_5027_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5026_, v___y_5016_, v___y_5019_);
lean_dec_ref(v___y_5024_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref(v___x_5031_);
v___y_4970_ = v___y_5018_;
v___y_4971_ = v___y_5023_;
v___y_4972_ = v___y_5025_;
v_body_4973_ = v_a_5032_;
v___y_4974_ = v___y_5027_;
v___y_4975_ = v___y_5020_;
v___y_4976_ = v___y_5021_;
v___y_4977_ = v___y_5022_;
v___y_4978_ = v___y_5026_;
v___y_4979_ = v___y_5016_;
v___y_4980_ = v___y_5019_;
goto v___jp_4969_;
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec(v___y_5025_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5016_);
lean_dec_ref(v_dec_4958_);
v_a_5033_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5031_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5031_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
}
v___jp_5041_:
{
lean_object* v___x_5054_; 
lean_inc(v___y_5045_);
lean_inc_ref(v___y_5042_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5048_);
lean_inc(v___y_5047_);
lean_inc_ref(v___y_5046_);
lean_inc(v___y_5052_);
v___x_5054_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5052_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5051_, v___y_5042_, v___y_5045_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_a_5055_; lean_object* v_letOrReassign_5056_; lean_object* v___x_5057_; 
v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5055_);
lean_dec_ref(v___x_5054_);
lean_inc(v___y_5043_);
v_letOrReassign_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_letOrReassign_5056_, 0, v___y_5043_);
lean_inc_ref(v___y_5042_);
v___x_5057_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_5056_, v_a_5055_, v___y_5050_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5051_, v___y_5042_, v___y_5045_);
lean_dec_ref(v_letOrReassign_5056_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_dec_ref(v___x_5057_);
if (lean_obj_tag(v___y_5053_) == 0)
{
lean_object* v_ref_5058_; lean_object* v_quotContext_5059_; lean_object* v_currMacroScope_5060_; lean_object* v___x_5061_; uint8_t v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v_ref_5058_ = lean_ctor_get(v___y_5042_, 5);
v_quotContext_5059_ = lean_ctor_get(v___y_5042_, 10);
v_currMacroScope_5060_ = lean_ctor_get(v___y_5042_, 11);
v___x_5061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5062_ = 0;
v___x_5063_ = l_Lean_SourceInfo_fromRef(v_ref_5058_, v___x_5062_);
v___x_5064_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5066_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5067_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5068_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5069_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc(v_currMacroScope_5060_);
lean_inc(v_quotContext_5059_);
v___x_5070_ = l_Lean_addMacroScope(v_quotContext_5059_, v___x_5069_, v_currMacroScope_5060_);
v___x_5071_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
lean_inc(v___x_5063_);
v___x_5072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5063_);
lean_ctor_set(v___x_5072_, 1, v___x_5068_);
lean_ctor_set(v___x_5072_, 2, v___x_5070_);
lean_ctor_set(v___x_5072_, 3, v___x_5071_);
v___x_5073_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5074_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
lean_inc(v_currMacroScope_5060_);
lean_inc(v_quotContext_5059_);
v___x_5075_ = l_Lean_addMacroScope(v_quotContext_5059_, v___x_5074_, v_currMacroScope_5060_);
v___x_5076_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
lean_inc(v___x_5063_);
v___x_5077_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5063_);
lean_ctor_set(v___x_5077_, 1, v___x_5073_);
lean_ctor_set(v___x_5077_, 2, v___x_5075_);
lean_ctor_set(v___x_5077_, 3, v___x_5076_);
lean_inc(v___x_5063_);
v___x_5078_ = l_Lean_Syntax_node1(v___x_5063_, v___x_5064_, v___x_5077_);
lean_inc(v___x_5063_);
v___x_5079_ = l_Lean_Syntax_node2(v___x_5063_, v___x_5067_, v___x_5072_, v___x_5078_);
lean_inc(v___x_5063_);
v___x_5080_ = l_Lean_Syntax_node1(v___x_5063_, v___x_5066_, v___x_5079_);
v___x_5081_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_5063_);
v___x_5082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5063_);
lean_ctor_set(v___x_5082_, 1, v___x_5064_);
lean_ctor_set(v___x_5082_, 2, v___x_5081_);
lean_inc(v___x_5063_);
v___x_5083_ = l_Lean_Syntax_node2(v___x_5063_, v___x_5065_, v___x_5080_, v___x_5082_);
lean_inc(v___x_5063_);
v___x_5084_ = l_Lean_Syntax_node1(v___x_5063_, v___x_5064_, v___x_5083_);
v___x_5085_ = l_Lean_Syntax_node1(v___x_5063_, v___x_5061_, v___x_5084_);
v___y_5016_ = v___y_5042_;
v___y_5017_ = v___y_5043_;
v___y_5018_ = v___y_5044_;
v___y_5019_ = v___y_5045_;
v___y_5020_ = v___y_5046_;
v___y_5021_ = v___y_5047_;
v___y_5022_ = v___y_5048_;
v___y_5023_ = v___y_5049_;
v___y_5024_ = v_a_5055_;
v___y_5025_ = v___y_5052_;
v___y_5026_ = v___y_5051_;
v___y_5027_ = v___y_5050_;
v_a_5028_ = v___x_5085_;
goto v___jp_5015_;
}
else
{
lean_object* v_val_5086_; 
v_val_5086_ = lean_ctor_get(v___y_5053_, 0);
lean_inc(v_val_5086_);
lean_dec_ref(v___y_5053_);
v___y_5016_ = v___y_5042_;
v___y_5017_ = v___y_5043_;
v___y_5018_ = v___y_5044_;
v___y_5019_ = v___y_5045_;
v___y_5020_ = v___y_5046_;
v___y_5021_ = v___y_5047_;
v___y_5022_ = v___y_5048_;
v___y_5023_ = v___y_5049_;
v___y_5024_ = v_a_5055_;
v___y_5025_ = v___y_5052_;
v___y_5026_ = v___y_5051_;
v___y_5027_ = v___y_5050_;
v_a_5028_ = v_val_5086_;
goto v___jp_5015_;
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_a_5055_);
lean_dec(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec_ref(v_dec_4958_);
v_a_5087_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5057_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5057_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec_ref(v_dec_4958_);
v_a_5095_ = lean_ctor_get(v___x_5054_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5054_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5054_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
v___jp_5103_:
{
lean_object* v___x_5112_; lean_object* v_pattern_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5112_ = lean_unsigned_to_nat(2u);
v_pattern_5113_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_5112_);
v___x_5114_ = lean_unsigned_to_nat(4u);
v___x_5115_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_5114_);
v___x_5116_ = lean_unsigned_to_nat(6u);
v___x_5117_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_5116_);
v___x_5118_ = lean_unsigned_to_nat(7u);
v___x_5119_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_5118_);
lean_dec(v_stx_4957_);
v___x_5120_ = l_Lean_Syntax_getOptional_x3f(v___x_5119_);
lean_dec(v___x_5119_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v___x_5121_; 
v___x_5121_ = lean_box(0);
v___y_5042_ = v___y_5110_;
v___y_5043_ = v_mutTk_x3f_5104_;
v___y_5044_ = v___x_5117_;
v___y_5045_ = v___y_5111_;
v___y_5046_ = v___y_5106_;
v___y_5047_ = v___y_5107_;
v___y_5048_ = v___y_5108_;
v___y_5049_ = v___x_5115_;
v___y_5050_ = v___y_5105_;
v___y_5051_ = v___y_5109_;
v___y_5052_ = v_pattern_5113_;
v___y_5053_ = v___x_5121_;
goto v___jp_5041_;
}
else
{
lean_object* v_val_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
v_val_5122_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5120_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_val_5122_);
lean_dec(v___x_5120_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_val_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
v___y_5042_ = v___y_5110_;
v___y_5043_ = v_mutTk_x3f_5104_;
v___y_5044_ = v___x_5117_;
v___y_5045_ = v___y_5111_;
v___y_5046_ = v___y_5106_;
v___y_5047_ = v___y_5107_;
v___y_5048_ = v___y_5108_;
v___y_5049_ = v___x_5115_;
v___y_5050_ = v___y_5105_;
v___y_5051_ = v___y_5109_;
v___y_5052_ = v_pattern_5113_;
v___y_5053_ = v___x_5127_;
goto v___jp_5041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5140_, lean_object* v_dec_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5140_, v_dec_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5151_, size_t v_sz_5152_, size_t v_i_5153_, lean_object* v_b_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5151_, v_sz_5152_, v_i_5153_, v_b_5154_, v___y_5160_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5164_, lean_object* v_sz_5165_, lean_object* v_i_5166_, lean_object* v_b_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
size_t v_sz_boxed_5176_; size_t v_i_boxed_5177_; lean_object* v_res_5178_; 
v_sz_boxed_5176_ = lean_unbox_usize(v_sz_5165_);
lean_dec(v_sz_5165_);
v_i_boxed_5177_ = lean_unbox_usize(v_i_5166_);
lean_dec(v_i_5166_);
v_res_5178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5164_, v_sz_boxed_5176_, v_i_boxed_5177_, v_b_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec_ref(v_as_5164_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5186_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5187_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5188_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5189_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5190_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5186_, v___x_5187_, v___x_5188_, v___x_5189_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5199_, lean_object* v_dec_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v_mutTk_x3f_5210_; lean_object* v___y_5211_; lean_object* v___y_5212_; lean_object* v___y_5213_; lean_object* v___y_5214_; lean_object* v___y_5215_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___x_5222_; uint8_t v___x_5223_; 
v___x_5222_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5199_);
v___x_5223_ = l_Lean_Syntax_isOfKind(v_stx_5199_, v___x_5222_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; 
lean_dec(v_a_5207_);
lean_dec_ref(v_a_5206_);
lean_dec(v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec(v_a_5203_);
lean_dec_ref(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec_ref(v_dec_5200_);
lean_dec(v_stx_5199_);
v___x_5224_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5224_;
}
else
{
lean_object* v___x_5225_; lean_object* v___x_5226_; uint8_t v___x_5227_; 
v___x_5225_ = lean_unsigned_to_nat(1u);
v___x_5226_ = l_Lean_Syntax_getArg(v_stx_5199_, v___x_5225_);
v___x_5227_ = l_Lean_Syntax_isNone(v___x_5226_);
if (v___x_5227_ == 0)
{
uint8_t v___x_5228_; 
lean_inc(v___x_5226_);
v___x_5228_ = l_Lean_Syntax_matchesNull(v___x_5226_, v___x_5225_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; 
lean_dec(v___x_5226_);
lean_dec(v_a_5207_);
lean_dec_ref(v_a_5206_);
lean_dec(v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec(v_a_5203_);
lean_dec_ref(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec_ref(v_dec_5200_);
lean_dec(v_stx_5199_);
v___x_5229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5229_;
}
else
{
lean_object* v___x_5230_; lean_object* v_mutTk_x3f_5231_; lean_object* v___x_5232_; 
v___x_5230_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5231_ = l_Lean_Syntax_getArg(v___x_5226_, v___x_5230_);
lean_dec(v___x_5226_);
v___x_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5232_, 0, v_mutTk_x3f_5231_);
v_mutTk_x3f_5210_ = v___x_5232_;
v___y_5211_ = v_a_5201_;
v___y_5212_ = v_a_5202_;
v___y_5213_ = v_a_5203_;
v___y_5214_ = v_a_5204_;
v___y_5215_ = v_a_5205_;
v___y_5216_ = v_a_5206_;
v___y_5217_ = v_a_5207_;
goto v___jp_5209_;
}
}
else
{
lean_object* v___x_5233_; 
lean_dec(v___x_5226_);
v___x_5233_ = lean_box(0);
v_mutTk_x3f_5210_ = v___x_5233_;
v___y_5211_ = v_a_5201_;
v___y_5212_ = v_a_5202_;
v___y_5213_ = v_a_5203_;
v___y_5214_ = v_a_5204_;
v___y_5215_ = v_a_5205_;
v___y_5216_ = v_a_5206_;
v___y_5217_ = v_a_5207_;
goto v___jp_5209_;
}
}
v___jp_5209_:
{
lean_object* v___x_5218_; lean_object* v_decl_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5218_ = lean_unsigned_to_nat(2u);
v_decl_5219_ = l_Lean_Syntax_getArg(v_stx_5199_, v___x_5218_);
lean_dec(v_stx_5199_);
v___x_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5220_, 0, v_mutTk_x3f_5210_);
v___x_5221_ = l_Lean_Elab_Do_elabDoArrow(v___x_5220_, v_decl_5219_, v_dec_5200_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
return v___x_5221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5234_, lean_object* v_dec_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5234_, v_dec_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5252_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5253_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5255_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5256_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5252_, v___x_5253_, v___x_5254_, v___x_5255_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5265_, lean_object* v_dec_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_){
_start:
{
lean_object* v___x_5275_; uint8_t v___x_5276_; 
v___x_5275_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5265_);
v___x_5276_ = l_Lean_Syntax_isOfKind(v_stx_5265_, v___x_5275_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; 
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec_ref(v_dec_5266_);
lean_dec(v_stx_5265_);
v___x_5277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5277_;
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; uint8_t v___x_5281_; 
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = l_Lean_Syntax_getArg(v_stx_5265_, v___x_5278_);
lean_dec(v_stx_5265_);
v___x_5280_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5279_);
v___x_5281_ = l_Lean_Syntax_isOfKind(v___x_5279_, v___x_5280_);
if (v___x_5281_ == 0)
{
lean_object* v___x_5282_; uint8_t v___x_5283_; 
v___x_5282_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5279_);
v___x_5283_ = l_Lean_Syntax_isOfKind(v___x_5279_, v___x_5282_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; 
lean_dec(v___x_5279_);
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec_ref(v_dec_5266_);
v___x_5284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5284_;
}
else
{
lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5285_ = lean_box(2);
v___x_5286_ = l_Lean_Elab_Do_elabDoArrow(v___x_5285_, v___x_5279_, v_dec_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_);
return v___x_5286_;
}
}
else
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = lean_box(2);
v___x_5288_ = l_Lean_Elab_Do_elabDoArrow(v___x_5287_, v___x_5279_, v_dec_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_);
return v___x_5288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5289_, lean_object* v_dec_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5289_, v_dec_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5307_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5308_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5309_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5310_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5311_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5307_, v___x_5308_, v___x_5309_, v___x_5310_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5313_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Let(builtin);
}
#ifdef __cplusplus
}
#endif
