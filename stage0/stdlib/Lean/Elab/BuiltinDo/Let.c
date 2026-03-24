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
lean_dec_ref(v_a_71_);
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
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
v___x_337_ = lean_apply_8(v_elabBody_327_, v_body_328_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object* v_elabBody_338_, lean_object* v_body_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(v_elabBody_338_, v_body_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
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
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_361_ = lean_apply_8(v_k_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
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
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec_ref(v___y_373_);
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
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_a_406_);
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
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec_ref(v_a_432_);
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
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
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
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
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
lean_inc_ref(v_a_713_);
v___x_725_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_724_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_806_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_805_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_813_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_812_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_856_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_855_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_863_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_862_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_717_);
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
lean_inc_ref(v_a_717_);
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
lean_dec_ref(v___y_738_);
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
lean_dec_ref(v___y_738_);
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
lean_inc_ref(v_a_713_);
v___x_873_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_872_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_965_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_964_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_972_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_971_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_980_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_979_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc_ref(v_a_713_);
v___x_987_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_986_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
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
lean_inc(v_x_874_);
v___x_885_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_874_, v_a_883_, v___x_721_, v___x_721_, v___x_884_, v___y_882_, v___y_881_, v___y_878_, v___y_880_, v___y_879_, v___y_877_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v___x_885_);
v___x_886_ = l_Lean_TSyntax_getId(v_x_874_);
v___x_887_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_886_, v___y_878_, v___y_880_, v___y_879_, v___y_877_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_LocalDecl_type(v_a_888_);
lean_dec(v_a_888_);
v___x_890_ = l_Lean_Elab_Term_exprToSyntax(v___x_889_, v___y_882_, v___y_881_, v___y_878_, v___y_880_, v___y_879_, v___y_877_);
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
v_ref_895_ = lean_ctor_get(v___y_879_, 5);
v___x_896_ = 0;
v___x_897_ = l_Lean_SourceInfo_fromRef(v_ref_895_, v___x_896_);
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
v___x_909_ = l_Lean_Syntax_node5(v___x_897_, v___x_728_, v___x_898_, v___x_901_, v___x_906_, v___x_908_, v___y_876_);
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
lean_dec(v___y_876_);
lean_dec(v_x_874_);
return v___x_890_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_876_);
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
lean_dec(v___y_876_);
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
v___y_876_ = v___x_940_;
v___y_877_ = v___y_938_;
v___y_878_ = v___y_935_;
v___y_879_ = v___y_937_;
v___y_880_ = v___y_936_;
v___y_881_ = v___y_934_;
v___y_882_ = v___y_933_;
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
v___y_876_ = v___x_940_;
v___y_877_ = v___y_938_;
v___y_878_ = v___y_935_;
v___y_879_ = v___y_937_;
v___y_880_ = v___y_936_;
v___y_881_ = v___y_934_;
v___y_882_ = v___y_933_;
v_a_883_ = v___x_949_;
goto v___jp_875_;
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_944_);
lean_dec(v___x_940_);
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
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_letOrReassign_992_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
lean_inc_ref(v___y_1004_);
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
lean_dec_ref(v___y_1014_);
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
lean_object* v_keyedConfig_1079_; uint8_t v_trackZetaDelta_1080_; lean_object* v_zetaDeltaSet_1081_; lean_object* v_localInstances_1082_; lean_object* v_defEqCtx_x3f_1083_; lean_object* v_synthPendingDepth_1084_; lean_object* v_canUnfold_x3f_1085_; uint8_t v_univApprox_1086_; uint8_t v_inTypeClassResolution_1087_; uint8_t v_cacheInferType_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
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
lean_inc(v_canUnfold_x3f_1085_);
lean_inc(v_synthPendingDepth_1084_);
lean_inc(v_defEqCtx_x3f_1083_);
lean_inc_ref(v_localInstances_1082_);
lean_inc(v_zetaDeltaSet_1081_);
lean_inc_ref(v_keyedConfig_1079_);
v___x_1089_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1089_, 0, v_keyedConfig_1079_);
lean_ctor_set(v___x_1089_, 1, v_zetaDeltaSet_1081_);
lean_ctor_set(v___x_1089_, 2, v_lctx_1070_);
lean_ctor_set(v___x_1089_, 3, v_localInstances_1082_);
lean_ctor_set(v___x_1089_, 4, v_defEqCtx_x3f_1083_);
lean_ctor_set(v___x_1089_, 5, v_synthPendingDepth_1084_);
lean_ctor_set(v___x_1089_, 6, v_canUnfold_x3f_1085_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7, v_trackZetaDelta_1080_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 1, v_univApprox_1086_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1087_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*7 + 3, v_cacheInferType_1088_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1090_ = lean_apply_7(v_x_1071_, v___y_1072_, v___y_1073_, v___x_1089_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1099_, v_x_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1109_, lean_object* v_lctx_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1110_, v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_lctx_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1120_, v_lctx_1121_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_options_1137_; uint8_t v_hasTrace_1138_; 
v_options_1137_ = lean_ctor_get(v___y_1135_, 2);
v_hasTrace_1138_ = lean_ctor_get_uint8(v_options_1137_, sizeof(void*)*1);
if (v_hasTrace_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_cls_1134_);
v___x_1139_ = lean_box(v_hasTrace_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v_inheritedTraceOptions_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_inheritedTraceOptions_1141_ = lean_ctor_get(v___y_1135_, 13);
v___x_1142_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_1143_ = l_Lean_Name_append(v___x_1142_, v_cls_1134_);
v___x_1144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1141_, v_options_1137_, v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_box(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_cls_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_1147_, v___y_1148_);
lean_dec_ref(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_1151_, v___y_1157_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0(lean_object* v_k_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc_ref(v___y_1172_);
v___x_1181_ = lean_apply_9(v_k_1171_, v_b_1175_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, lean_box(0));
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0___boxed(lean_object* v_k_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0(v_k_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_name_1193_, lean_object* v_type_1194_, lean_object* v_val_1195_, lean_object* v_k_1196_, uint8_t v_nondep_1197_, uint8_t v_kind_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc_ref(v___y_1199_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1207_, 0, v_k_1196_);
lean_closure_set(v___f_1207_, 1, v___y_1199_);
lean_closure_set(v___f_1207_, 2, v___y_1200_);
lean_closure_set(v___f_1207_, 3, v___y_1201_);
v___x_1208_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1193_, v_type_1194_, v_val_1195_, v___f_1207_, v_nondep_1197_, v_kind_1198_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1208_) == 0)
{
return v___x_1208_;
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_name_1217_, lean_object* v_type_1218_, lean_object* v_val_1219_, lean_object* v_k_1220_, lean_object* v_nondep_1221_, lean_object* v_kind_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_nondep_boxed_1231_; uint8_t v_kind_boxed_1232_; lean_object* v_res_1233_; 
v_nondep_boxed_1231_ = lean_unbox(v_nondep_1221_);
v_kind_boxed_1232_ = lean_unbox(v_kind_1222_);
v_res_1233_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_name_1217_, v_type_1218_, v_val_1219_, v_k_1220_, v_nondep_boxed_1231_, v_kind_boxed_1232_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_00_u03b1_1234_, lean_object* v_name_1235_, lean_object* v_type_1236_, lean_object* v_val_1237_, lean_object* v_k_1238_, uint8_t v_nondep_1239_, uint8_t v_kind_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_name_1235_, v_type_1236_, v_val_1237_, v_k_1238_, v_nondep_1239_, v_kind_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_name_1251_, lean_object* v_type_1252_, lean_object* v_val_1253_, lean_object* v_k_1254_, lean_object* v_nondep_1255_, lean_object* v_kind_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_nondep_boxed_1265_; uint8_t v_kind_boxed_1266_; lean_object* v_res_1267_; 
v_nondep_boxed_1265_ = lean_unbox(v_nondep_1255_);
v_kind_boxed_1266_ = lean_unbox(v_kind_1256_);
v_res_1267_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_00_u03b1_1250_, v_name_1251_, v_type_1252_, v_val_1253_, v_k_1254_, v_nondep_boxed_1265_, v_kind_boxed_1266_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1268_, lean_object* v___x_1269_, uint8_t v___x_1270_, lean_object* v___x_1271_, lean_object* v___x_1272_, uint8_t v___x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1268_, v___x_1269_, v___x_1270_, v___x_1270_, v___x_1271_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = 1;
v___x_1284_ = l_Lean_Meta_mkLambdaFVars(v___x_1272_, v_a_1282_, v___x_1273_, v___x_1273_, v___x_1273_, v___x_1270_, v___x_1283_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1284_;
}
else
{
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1285_, lean_object* v___x_1286_, lean_object* v___x_1287_, lean_object* v___x_1288_, lean_object* v___x_1289_, lean_object* v___x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_74150__boxed_1298_; uint8_t v___x_74153__boxed_1299_; lean_object* v_res_1300_; 
v___x_74150__boxed_1298_ = lean_unbox(v___x_1287_);
v___x_74153__boxed_1299_ = lean_unbox(v___x_1290_);
v_res_1300_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1285_, v___x_1286_, v___x_74150__boxed_1298_, v___x_1288_, v___x_1289_, v___x_74153__boxed_1299_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v___x_1289_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v_ks_1305_; lean_object* v_vs_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1330_; 
v_ks_1305_ = lean_ctor_get(v_x_1301_, 0);
v_vs_1306_ = lean_ctor_get(v_x_1301_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1308_ = v_x_1301_;
v_isShared_1309_ = v_isSharedCheck_1330_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_vs_1306_);
lean_inc(v_ks_1305_);
lean_dec(v_x_1301_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1330_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_array_get_size(v_ks_1305_);
v___x_1311_ = lean_nat_dec_lt(v_x_1302_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec(v_x_1302_);
v___x_1312_ = lean_array_push(v_ks_1305_, v_x_1303_);
v___x_1313_ = lean_array_push(v_vs_1306_, v_x_1304_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1313_);
lean_ctor_set(v___x_1308_, 0, v___x_1312_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
else
{
lean_object* v_k_x27_1317_; uint8_t v___x_1318_; 
v_k_x27_1317_ = lean_array_fget_borrowed(v_ks_1305_, v_x_1302_);
v___x_1318_ = l_Lean_instBEqFVarId_beq(v_x_1303_, v_k_x27_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1320_; 
if (v_isShared_1309_ == 0)
{
v___x_1320_ = v___x_1308_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_ks_1305_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_vs_1306_);
v___x_1320_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v_x_1302_, v___x_1321_);
lean_dec(v_x_1302_);
v_x_1301_ = v___x_1320_;
v_x_1302_ = v___x_1322_;
goto _start;
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = lean_array_fset(v_ks_1305_, v_x_1302_, v_x_1303_);
v___x_1326_ = lean_array_fset(v_vs_1306_, v_x_1302_, v_x_1304_);
lean_dec(v_x_1302_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1326_);
lean_ctor_set(v___x_1308_, 0, v___x_1325_);
v___x_1328_ = v___x_1308_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(lean_object* v_n_1331_, lean_object* v_k_1332_, lean_object* v_v_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(v_n_1331_, v___x_1334_, v_k_1332_, v_v_1333_);
return v___x_1335_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; 
v___x_1336_ = ((size_t)5ULL);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_shift_left(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; 
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1341_ = lean_usize_sub(v___x_1340_, v___x_1339_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1343_, size_t v_x_1344_, size_t v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
lean_object* v_es_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v_j_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_es_1348_ = lean_ctor_get(v_x_1343_, 0);
v___x_1349_ = ((size_t)5ULL);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_1352_ = lean_usize_land(v_x_1344_, v___x_1351_);
v_j_1353_ = lean_usize_to_nat(v___x_1352_);
v___x_1354_ = lean_array_get_size(v_es_1348_);
v___x_1355_ = lean_nat_dec_lt(v_j_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec(v_j_1353_);
lean_dec(v_x_1347_);
lean_dec(v_x_1346_);
return v_x_1343_;
}
else
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1392_; 
lean_inc_ref(v_es_1348_);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_x_1343_, 0);
lean_dec(v_unused_1393_);
v___x_1357_ = v_x_1343_;
v_isShared_1358_ = v_isSharedCheck_1392_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v_x_1343_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1392_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_v_1359_; lean_object* v___x_1360_; lean_object* v_xs_x27_1361_; lean_object* v___y_1363_; 
v_v_1359_ = lean_array_fget(v_es_1348_, v_j_1353_);
v___x_1360_ = lean_box(0);
v_xs_x27_1361_ = lean_array_fset(v_es_1348_, v_j_1353_, v___x_1360_);
switch(lean_obj_tag(v_v_1359_))
{
case 0:
{
lean_object* v_key_1368_; lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1379_; 
v_key_1368_ = lean_ctor_get(v_v_1359_, 0);
v_val_1369_ = lean_ctor_get(v_v_1359_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_v_1359_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1371_ = v_v_1359_;
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_inc(v_key_1368_);
lean_dec(v_v_1359_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1379_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; 
v___x_1373_ = l_Lean_instBEqFVarId_beq(v_x_1346_, v_key_1368_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_del_object(v___x_1371_);
v___x_1374_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1368_, v_val_1369_, v_x_1346_, v_x_1347_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___y_1363_ = v___x_1375_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_val_1369_);
lean_dec(v_key_1368_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_x_1347_);
lean_ctor_set(v___x_1371_, 0, v_x_1346_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_x_1346_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_x_1347_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v___y_1363_ = v___x_1377_;
goto v___jp_1362_;
}
}
}
}
case 1:
{
lean_object* v_node_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1390_; 
v_node_1380_ = lean_ctor_get(v_v_1359_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_v_1359_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1382_ = v_v_1359_;
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_node_1380_);
lean_dec(v_v_1359_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1384_ = lean_usize_shift_right(v_x_1344_, v___x_1349_);
v___x_1385_ = lean_usize_add(v_x_1345_, v___x_1350_);
v___x_1386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1380_, v___x_1384_, v___x_1385_, v_x_1346_, v_x_1347_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1386_);
v___x_1388_ = v___x_1382_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v___y_1363_ = v___x_1388_;
goto v___jp_1362_;
}
}
}
default: 
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_x_1346_);
lean_ctor_set(v___x_1391_, 1, v_x_1347_);
v___y_1363_ = v___x_1391_;
goto v___jp_1362_;
}
}
v___jp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_array_fset(v_xs_x27_1361_, v_j_1353_, v___y_1363_);
lean_dec(v_j_1353_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1364_);
v___x_1366_ = v___x_1357_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_ks_1394_; lean_object* v_vs_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1415_; 
v_ks_1394_ = lean_ctor_get(v_x_1343_, 0);
v_vs_1395_ = lean_ctor_get(v_x_1343_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1397_ = v_x_1343_;
v_isShared_1398_ = v_isSharedCheck_1415_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_vs_1395_);
lean_inc(v_ks_1394_);
lean_dec(v_x_1343_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1415_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_ks_1394_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_vs_1395_);
v___x_1400_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v_newNode_1401_; uint8_t v___y_1403_; size_t v___x_1409_; uint8_t v___x_1410_; 
v_newNode_1401_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v___x_1400_, v_x_1346_, v_x_1347_);
v___x_1409_ = ((size_t)7ULL);
v___x_1410_ = lean_usize_dec_le(v___x_1409_, v_x_1345_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1401_);
v___x_1412_ = lean_unsigned_to_nat(4u);
v___x_1413_ = lean_nat_dec_lt(v___x_1411_, v___x_1412_);
lean_dec(v___x_1411_);
v___y_1403_ = v___x_1413_;
goto v___jp_1402_;
}
else
{
v___y_1403_ = v___x_1410_;
goto v___jp_1402_;
}
v___jp_1402_:
{
if (v___y_1403_ == 0)
{
lean_object* v_ks_1404_; lean_object* v_vs_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_ks_1404_ = lean_ctor_get(v_newNode_1401_, 0);
lean_inc_ref(v_ks_1404_);
v_vs_1405_ = lean_ctor_get(v_newNode_1401_, 1);
lean_inc_ref(v_vs_1405_);
lean_dec_ref(v_newNode_1401_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2);
v___x_1408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_x_1345_, v_ks_1404_, v_vs_1405_, v___x_1406_, v___x_1407_);
lean_dec_ref(v_vs_1405_);
lean_dec_ref(v_ks_1404_);
return v___x_1408_;
}
else
{
return v_newNode_1401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(size_t v_depth_1416_, lean_object* v_keys_1417_, lean_object* v_vals_1418_, lean_object* v_i_1419_, lean_object* v_entries_1420_){
_start:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_array_get_size(v_keys_1417_);
v___x_1422_ = lean_nat_dec_lt(v_i_1419_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_dec(v_i_1419_);
return v_entries_1420_;
}
else
{
lean_object* v_k_1423_; lean_object* v_v_1424_; uint64_t v___x_1425_; size_t v_h_1426_; size_t v___x_1427_; lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; size_t v_h_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_k_1423_ = lean_array_fget_borrowed(v_keys_1417_, v_i_1419_);
v_v_1424_ = lean_array_fget_borrowed(v_vals_1418_, v_i_1419_);
v___x_1425_ = l_Lean_instHashableFVarId_hash(v_k_1423_);
v_h_1426_ = lean_uint64_to_usize(v___x_1425_);
v___x_1427_ = ((size_t)5ULL);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_sub(v_depth_1416_, v___x_1429_);
v___x_1431_ = lean_usize_mul(v___x_1427_, v___x_1430_);
v_h_1432_ = lean_usize_shift_right(v_h_1426_, v___x_1431_);
v___x_1433_ = lean_nat_add(v_i_1419_, v___x_1428_);
lean_dec(v_i_1419_);
lean_inc(v_v_1424_);
lean_inc(v_k_1423_);
v___x_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1420_, v_h_1432_, v_depth_1416_, v_k_1423_, v_v_1424_);
v_i_1419_ = v___x_1433_;
v_entries_1420_ = v___x_1434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_depth_1436_, lean_object* v_keys_1437_, lean_object* v_vals_1438_, lean_object* v_i_1439_, lean_object* v_entries_1440_){
_start:
{
size_t v_depth_boxed_1441_; lean_object* v_res_1442_; 
v_depth_boxed_1441_ = lean_unbox_usize(v_depth_1436_);
lean_dec(v_depth_1436_);
v_res_1442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_depth_boxed_1441_, v_keys_1437_, v_vals_1438_, v_i_1439_, v_entries_1440_);
lean_dec_ref(v_vals_1438_);
lean_dec_ref(v_keys_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
size_t v_x_74285__boxed_1448_; size_t v_x_74286__boxed_1449_; lean_object* v_res_1450_; 
v_x_74285__boxed_1448_ = lean_unbox_usize(v_x_1444_);
lean_dec(v_x_1444_);
v_x_74286__boxed_1449_ = lean_unbox_usize(v_x_1445_);
lean_dec(v_x_1445_);
v_res_1450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1443_, v_x_74285__boxed_1448_, v_x_74286__boxed_1449_, v_x_1446_, v_x_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
uint64_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = l_Lean_instHashableFVarId_hash(v_x_1452_);
v___x_1455_ = lean_uint64_to_usize(v___x_1454_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1451_, v___x_1455_, v___x_1456_, v_x_1452_, v_x_1453_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_, lean_object* v_b_1461_){
_start:
{
lean_object* v___y_1463_; uint8_t v___x_1467_; 
v___x_1467_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1467_ == 0)
{
lean_object* v_fvarIdToDecl_1468_; lean_object* v_decls_1469_; lean_object* v_auxDeclToFullName_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_fvarIdToDecl_1468_ = lean_ctor_get(v_b_1461_, 0);
v_decls_1469_ = lean_ctor_get(v_b_1461_, 1);
v_auxDeclToFullName_1470_ = lean_ctor_get(v_b_1461_, 2);
v___x_1471_ = lean_array_uget_borrowed(v_as_1458_, v_i_1459_);
v___x_1472_ = l_Lean_Expr_fvarId_x21(v___x_1471_);
lean_inc_ref(v_b_1461_);
v___x_1473_ = lean_local_ctx_find(v_b_1461_, v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
v___y_1463_ = v_b_1461_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1500_; 
lean_inc(v_auxDeclToFullName_1470_);
lean_inc_ref(v_decls_1469_);
lean_inc_ref(v_fvarIdToDecl_1468_);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_b_1461_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; 
v_unused_1501_ = lean_ctor_get(v_b_1461_, 2);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_b_1461_, 1);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_b_1461_, 0);
lean_dec(v_unused_1503_);
v___x_1475_ = v_b_1461_;
v_isShared_1476_ = v_isSharedCheck_1500_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_b_1461_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1500_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_val_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1499_; 
v_val_1477_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1479_ = v___x_1473_;
v_isShared_1480_ = v_isSharedCheck_1499_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_val_1477_);
lean_dec(v___x_1473_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1499_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1495_; lean_object* v_fvarId_1498_; 
v___x_1481_ = l_Lean_LocalDecl_type(v_val_1477_);
v___x_1482_ = l_Lean_Expr_cleanupAnnotations(v___x_1481_);
v___x_1483_ = l_Lean_LocalDecl_setType(v_val_1477_, v___x_1482_);
v_fvarId_1498_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_fvarId_1498_);
v___y_1495_ = v_fvarId_1498_;
goto v___jp_1494_;
v___jp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1483_);
v___x_1488_ = v___x_1479_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1483_);
v___x_1488_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = l_Lean_PersistentArray_set___redArg(v_decls_1469_, v___y_1486_, v___x_1488_);
lean_dec(v___y_1486_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1489_);
lean_ctor_set(v___x_1475_, 0, v___y_1485_);
v___x_1491_ = v___x_1475_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___y_1485_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_auxDeclToFullName_1470_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
v___y_1463_ = v___x_1491_;
goto v___jp_1462_;
}
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v_index_1497_; 
lean_inc_ref(v___x_1483_);
v___x_1496_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1468_, v___y_1495_, v___x_1483_);
v_index_1497_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_index_1497_);
v___y_1485_ = v___x_1496_;
v___y_1486_ = v_index_1497_;
goto v___jp_1484_;
}
}
}
}
}
else
{
return v_b_1461_;
}
v___jp_1462_:
{
size_t v___x_1464_; size_t v___x_1465_; 
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1459_, v___x_1464_);
v_i_1459_ = v___x_1465_;
v_b_1461_ = v___y_1463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1504_, lean_object* v_i_1505_, lean_object* v_stop_1506_, lean_object* v_b_1507_){
_start:
{
size_t v_i_boxed_1508_; size_t v_stop_boxed_1509_; lean_object* v_res_1510_; 
v_i_boxed_1508_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_stop_boxed_1509_ = lean_unbox_usize(v_stop_1506_);
lean_dec(v_stop_1506_);
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1504_, v_i_boxed_1508_, v_stop_boxed_1509_, v_b_1507_);
lean_dec_ref(v_as_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1514_ == 0)
{
return v_bs_1513_;
}
else
{
lean_object* v_v_1515_; lean_object* v_snd_1516_; lean_object* v___x_1517_; lean_object* v_bs_x27_1518_; size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v_v_1515_ = lean_array_uget_borrowed(v_bs_1513_, v_i_1512_);
v_snd_1516_ = lean_ctor_get(v_v_1515_, 1);
lean_inc(v_snd_1516_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v_bs_x27_1518_ = lean_array_uset(v_bs_1513_, v_i_1512_, v___x_1517_);
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1512_, v___x_1519_);
v___x_1521_ = lean_array_uset(v_bs_x27_1518_, v_i_1512_, v_snd_1516_);
v_i_1512_ = v___x_1520_;
v_bs_1513_ = v___x_1521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_bs_1525_){
_start:
{
size_t v_sz_boxed_1526_; size_t v_i_boxed_1527_; lean_object* v_res_1528_; 
v_sz_boxed_1526_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1527_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1526_, v_i_boxed_1527_, v_bs_1525_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1540_, lean_object* v_value_1541_, uint8_t v___x_1542_, uint8_t v___x_1543_, lean_object* v___x_1544_, uint8_t v___y_1545_, lean_object* v_xs_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
lean_inc(v_type_1540_);
v___x_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1554_, 0, v_type_1540_);
v___x_1555_ = 2;
v___x_1556_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1554_, v___x_1555_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___y_1562_; lean_object* v___y_1598_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v_sz_1558_ = lean_array_size(v_xs_1546_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1558_, v___x_1559_, v_xs_1546_);
if (v___y_1545_ == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1598_ = v___x_1634_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1598_ = v___x_1635_;
goto v___jp_1597_;
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; 
lean_inc(v_a_1557_);
v___x_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1563_, 0, v_a_1557_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_box(v___x_1542_);
v___x_1566_ = lean_box(v___x_1543_);
lean_inc_ref(v___x_1560_);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1567_, 0, v_value_1541_);
lean_closure_set(v___f_1567_, 1, v___x_1563_);
lean_closure_set(v___f_1567_, 2, v___x_1565_);
lean_closure_set(v___f_1567_, 3, v___x_1564_);
lean_closure_set(v___f_1567_, 4, v___x_1560_);
lean_closure_set(v___f_1567_, 5, v___x_1566_);
v___x_1568_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1562_, v___f_1567_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = 1;
v___x_1571_ = l_Lean_Meta_mkForallFVars(v___x_1560_, v_a_1557_, v___x_1543_, v___x_1542_, v___x_1542_, v___x_1570_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1572_);
lean_ctor_set(v___x_1576_, 1, v_a_1569_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1569_);
v_a_1581_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1571_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1571_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___x_1560_);
lean_dec(v_a_1557_);
lean_dec_ref(v___y_1549_);
v_a_1589_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1568_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1568_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
v___jp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
v___x_1600_ = l_Lean_stringToMessageData(v___y_1598_);
lean_inc_ref(v___x_1600_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
lean_inc(v_type_1540_);
v___x_1604_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1557_, v_type_1540_, v___x_1603_, v___y_1548_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v___x_1604_);
v___x_1605_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1600_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___x_1602_);
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_inc(v_a_1557_);
v___x_1609_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1557_, v_type_1540_, v___x_1608_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_lctx_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
lean_dec_ref(v___x_1609_);
v_lctx_1610_ = lean_ctor_get(v___y_1549_, 2);
v___x_1611_ = lean_array_get_size(v___x_1560_);
v___x_1612_ = lean_nat_dec_lt(v___x_1544_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_inc_ref(v_lctx_1610_);
v___y_1562_ = v_lctx_1610_;
goto v___jp_1561_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_le(v___x_1611_, v___x_1611_);
if (v___x_1613_ == 0)
{
if (v___x_1612_ == 0)
{
lean_inc_ref(v_lctx_1610_);
v___y_1562_ = v_lctx_1610_;
goto v___jp_1561_;
}
else
{
size_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_usize_of_nat(v___x_1611_);
lean_inc_ref(v_lctx_1610_);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1560_, v___x_1559_, v___x_1614_, v_lctx_1610_);
v___y_1562_ = v___x_1615_;
goto v___jp_1561_;
}
}
else
{
size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_usize_of_nat(v___x_1611_);
lean_inc_ref(v_lctx_1610_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1560_, v___x_1559_, v___x_1616_, v_lctx_1610_);
v___y_1562_ = v___x_1617_;
goto v___jp_1561_;
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v___x_1560_);
lean_dec(v_a_1557_);
lean_dec_ref(v___y_1549_);
lean_dec(v_value_1541_);
v_a_1618_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1609_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1609_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v___x_1600_);
lean_dec_ref(v___x_1560_);
lean_dec(v_a_1557_);
lean_dec_ref(v___y_1549_);
lean_dec(v_value_1541_);
lean_dec(v_type_1540_);
v_a_1626_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1604_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1604_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_xs_1546_);
lean_dec(v_value_1541_);
lean_dec(v_type_1540_);
v_a_1636_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1556_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1556_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1644_, lean_object* v_value_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v___x_1648_, lean_object* v___y_1649_, lean_object* v_xs_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v___x_74604__boxed_1658_; uint8_t v___x_74605__boxed_1659_; uint8_t v___y_74607__boxed_1660_; lean_object* v_res_1661_; 
v___x_74604__boxed_1658_ = lean_unbox(v___x_1646_);
v___x_74605__boxed_1659_ = lean_unbox(v___x_1647_);
v___y_74607__boxed_1660_ = lean_unbox(v___y_1649_);
v_res_1661_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1644_, v_value_1645_, v___x_74604__boxed_1658_, v___x_74605__boxed_1659_, v___x_1648_, v___y_74607__boxed_1660_, v_xs_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___x_1648_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_dec_1662_, lean_object* v_x_1663_, uint8_t v___x_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_1662_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_mk_empty_array_with_capacity(v___x_1675_);
v___x_1677_ = lean_array_push(v___x_1676_, v_x_1663_);
v___x_1678_ = 1;
v___x_1679_ = l_Lean_Meta_mkLetFVars(v___x_1677_, v_a_1674_, v___x_1664_, v___x_1664_, v___x_1678_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec_ref(v___x_1677_);
return v___x_1679_;
}
else
{
lean_dec_ref(v_x_1663_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object* v_dec_1680_, lean_object* v_x_1681_, lean_object* v___x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_74829__boxed_1691_; lean_object* v_res_1692_; 
v___x_74829__boxed_1691_ = lean_unbox(v___x_1682_);
v_res_1692_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_dec_1680_, v_x_1681_, v___x_74829__boxed_1691_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_1693_, lean_object* v_dec_1694_, uint8_t v___x_1695_, lean_object* v_letOrReassign_1696_, lean_object* v_a_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
lean_inc_ref(v_x_1698_);
v___x_1707_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1693_, v_x_1698_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; 
lean_dec_ref(v___x_1707_);
v___x_1708_ = lean_box(v___x_1695_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 11, 3);
lean_closure_set(v___f_1709_, 0, v_dec_1694_);
lean_closure_set(v___f_1709_, 1, v_x_1698_);
lean_closure_set(v___f_1709_, 2, v___x_1708_);
v___x_1710_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1696_, v_a_1697_, v___f_1709_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1710_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v_x_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_letOrReassign_1696_);
lean_dec_ref(v_dec_1694_);
v_a_1711_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1707_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1707_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object* v_id_1719_, lean_object* v_dec_1720_, lean_object* v___x_1721_, lean_object* v_letOrReassign_1722_, lean_object* v_a_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_74871__boxed_1733_; lean_object* v_res_1734_; 
v___x_74871__boxed_1733_ = lean_unbox(v___x_1721_);
v_res_1734_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_1719_, v_dec_1720_, v___x_74871__boxed_1733_, v_letOrReassign_1722_, v_a_1723_, v_x_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v___x_1735_, lean_object* v___x_1736_, uint8_t v___x_1737_, lean_object* v___x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1735_, v___x_1736_, v___x_1737_, v___x_1737_, v___x_1738_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___x_74928__boxed_1760_; lean_object* v_res_1761_; 
v___x_74928__boxed_1760_ = lean_unbox(v___x_1750_);
v_res_1761_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_1748_, v___x_1749_, v___x_74928__boxed_1760_, v___x_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
lean_inc_ref(v___y_1763_);
v___x_1771_ = lean_apply_8(v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, lean_box(0));
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_x_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec_ref(v___y_1773_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0(lean_object* v_stx_1782_, lean_object* v_output_1783_, lean_object* v_trees_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_lctx_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_lctx_1792_ = lean_ctor_get(v___y_1787_, 2);
lean_inc_ref(v_lctx_1792_);
v___x_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1793_, 0, v_lctx_1792_);
lean_ctor_set(v___x_1793_, 1, v_stx_1782_);
lean_ctor_set(v___x_1793_, 2, v_output_1783_);
v___x_1794_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_trees_1784_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_stx_1797_, lean_object* v_output_1798_, lean_object* v_trees_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0(v_stx_1797_, v_output_1798_, v_trees_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v_infoState_1811_; lean_object* v_trees_1812_; lean_object* v___x_1813_; lean_object* v_infoState_1814_; lean_object* v_env_1815_; lean_object* v_nextMacroScope_1816_; lean_object* v_ngen_1817_; lean_object* v_auxDeclNGen_1818_; lean_object* v_traceState_1819_; lean_object* v_cache_1820_; lean_object* v_messages_1821_; lean_object* v_snapshotTasks_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1845_; 
v___x_1810_ = lean_st_ref_get(v___y_1808_);
v_infoState_1811_ = lean_ctor_get(v___x_1810_, 7);
lean_inc_ref(v_infoState_1811_);
lean_dec(v___x_1810_);
v_trees_1812_ = lean_ctor_get(v_infoState_1811_, 2);
lean_inc_ref(v_trees_1812_);
lean_dec_ref(v_infoState_1811_);
v___x_1813_ = lean_st_ref_take(v___y_1808_);
v_infoState_1814_ = lean_ctor_get(v___x_1813_, 7);
v_env_1815_ = lean_ctor_get(v___x_1813_, 0);
v_nextMacroScope_1816_ = lean_ctor_get(v___x_1813_, 1);
v_ngen_1817_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1818_ = lean_ctor_get(v___x_1813_, 3);
v_traceState_1819_ = lean_ctor_get(v___x_1813_, 4);
v_cache_1820_ = lean_ctor_get(v___x_1813_, 5);
v_messages_1821_ = lean_ctor_get(v___x_1813_, 6);
v_snapshotTasks_1822_ = lean_ctor_get(v___x_1813_, 8);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1824_ = v___x_1813_;
v_isShared_1825_ = v_isSharedCheck_1845_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_snapshotTasks_1822_);
lean_inc(v_infoState_1814_);
lean_inc(v_messages_1821_);
lean_inc(v_cache_1820_);
lean_inc(v_traceState_1819_);
lean_inc(v_auxDeclNGen_1818_);
lean_inc(v_ngen_1817_);
lean_inc(v_nextMacroScope_1816_);
lean_inc(v_env_1815_);
lean_dec(v___x_1813_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1845_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint8_t v_enabled_1826_; lean_object* v_assignment_1827_; lean_object* v_lazyAssignment_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1843_; 
v_enabled_1826_ = lean_ctor_get_uint8(v_infoState_1814_, sizeof(void*)*3);
v_assignment_1827_ = lean_ctor_get(v_infoState_1814_, 0);
v_lazyAssignment_1828_ = lean_ctor_get(v_infoState_1814_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_infoState_1814_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_infoState_1814_, 2);
lean_dec(v_unused_1844_);
v___x_1830_ = v_infoState_1814_;
v_isShared_1831_ = v_isSharedCheck_1843_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_lazyAssignment_1828_);
lean_inc(v_assignment_1827_);
lean_dec(v_infoState_1814_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1843_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1832_ = lean_unsigned_to_nat(32u);
v___x_1833_ = lean_mk_empty_array_with_capacity(v___x_1832_);
lean_dec_ref(v___x_1833_);
v___x_1834_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 2, v___x_1834_);
v___x_1836_ = v___x_1830_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_assignment_1827_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_lazyAssignment_1828_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v___x_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*3, v_enabled_1826_);
v___x_1836_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 7, v___x_1836_);
v___x_1838_ = v___x_1824_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1815_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_nextMacroScope_1816_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_ngen_1817_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_auxDeclNGen_1818_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_traceState_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_cache_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_messages_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_snapshotTasks_1822_);
v___x_1838_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_st_ref_set(v___y_1808_, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_trees_1812_);
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg___boxed(lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_1846_);
lean_dec(v___y_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(lean_object* v___y_1849_, lean_object* v_mkInfoTree_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v_a_1856_, lean_object* v_a_x3f_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v_infoState_1860_; lean_object* v_trees_1861_; lean_object* v___x_1862_; 
v___x_1859_ = lean_st_ref_get(v___y_1849_);
v_infoState_1860_ = lean_ctor_get(v___x_1859_, 7);
lean_inc_ref(v_infoState_1860_);
lean_dec(v___x_1859_);
v_trees_1861_ = lean_ctor_get(v_infoState_1860_, 2);
lean_inc_ref(v_trees_1861_);
lean_dec_ref(v_infoState_1860_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
v___x_1862_ = lean_apply_8(v_mkInfoTree_1850_, v_trees_1861_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1849_, lean_box(0));
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1901_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1901_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1901_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v_infoState_1868_; lean_object* v_env_1869_; lean_object* v_nextMacroScope_1870_; lean_object* v_ngen_1871_; lean_object* v_auxDeclNGen_1872_; lean_object* v_traceState_1873_; lean_object* v_cache_1874_; lean_object* v_messages_1875_; lean_object* v_snapshotTasks_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1900_; 
v___x_1867_ = lean_st_ref_take(v___y_1849_);
v_infoState_1868_ = lean_ctor_get(v___x_1867_, 7);
v_env_1869_ = lean_ctor_get(v___x_1867_, 0);
v_nextMacroScope_1870_ = lean_ctor_get(v___x_1867_, 1);
v_ngen_1871_ = lean_ctor_get(v___x_1867_, 2);
v_auxDeclNGen_1872_ = lean_ctor_get(v___x_1867_, 3);
v_traceState_1873_ = lean_ctor_get(v___x_1867_, 4);
v_cache_1874_ = lean_ctor_get(v___x_1867_, 5);
v_messages_1875_ = lean_ctor_get(v___x_1867_, 6);
v_snapshotTasks_1876_ = lean_ctor_get(v___x_1867_, 8);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1878_ = v___x_1867_;
v_isShared_1879_ = v_isSharedCheck_1900_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_snapshotTasks_1876_);
lean_inc(v_infoState_1868_);
lean_inc(v_messages_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1873_);
lean_inc(v_auxDeclNGen_1872_);
lean_inc(v_ngen_1871_);
lean_inc(v_nextMacroScope_1870_);
lean_inc(v_env_1869_);
lean_dec(v___x_1867_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1900_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
uint8_t v_enabled_1880_; lean_object* v_assignment_1881_; lean_object* v_lazyAssignment_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1898_; 
v_enabled_1880_ = lean_ctor_get_uint8(v_infoState_1868_, sizeof(void*)*3);
v_assignment_1881_ = lean_ctor_get(v_infoState_1868_, 0);
v_lazyAssignment_1882_ = lean_ctor_get(v_infoState_1868_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_infoState_1868_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_infoState_1868_, 2);
lean_dec(v_unused_1899_);
v___x_1884_ = v_infoState_1868_;
v_isShared_1885_ = v_isSharedCheck_1898_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_lazyAssignment_1882_);
lean_inc(v_assignment_1881_);
lean_dec(v_infoState_1868_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1898_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_PersistentArray_push___redArg(v_a_1856_, v_a_1863_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_assignment_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_lazyAssignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v___x_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*3, v_enabled_1880_);
v___x_1888_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 7, v___x_1888_);
v___x_1890_ = v___x_1878_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_env_1869_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_nextMacroScope_1870_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_ngen_1871_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_auxDeclNGen_1872_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_traceState_1873_);
lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_messages_1875_);
lean_ctor_set(v_reuseFailAlloc_1896_, 7, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 8, v_snapshotTasks_1876_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = lean_st_ref_set(v___y_1849_, v___x_1890_);
v___x_1892_ = lean_box(0);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1892_);
v___x_1894_ = v___x_1865_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref(v_a_1856_);
v_a_1902_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1862_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1862_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0___boxed(lean_object* v___y_1910_, lean_object* v_mkInfoTree_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v_a_1917_, lean_object* v_a_x3f_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1910_, v_mkInfoTree_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v_a_1917_, v_a_x3f_1918_);
lean_dec(v_a_x3f_1918_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1910_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(lean_object* v_x_1921_, lean_object* v_mkInfoTree_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_infoState_1931_; uint8_t v_enabled_1932_; 
v___x_1930_ = lean_st_ref_get(v___y_1928_);
v_infoState_1931_ = lean_ctor_get(v___x_1930_, 7);
lean_inc_ref(v_infoState_1931_);
lean_dec(v___x_1930_);
v_enabled_1932_ = lean_ctor_get_uint8(v_infoState_1931_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1931_);
if (v_enabled_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_dec_ref(v_mkInfoTree_1922_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
v___x_1933_ = lean_apply_7(v_x_1921_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
return v___x_1933_;
}
else
{
lean_object* v___x_1934_; lean_object* v_a_1935_; lean_object* v_r_1936_; 
v___x_1934_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_1928_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
v_r_1936_ = lean_apply_7(v_x_1921_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
if (lean_obj_tag(v_r_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1961_; 
v_a_1937_ = lean_ctor_get(v_r_1936_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_r_1936_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1939_ = v_r_1936_;
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v_r_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
lean_inc(v_a_1937_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 1);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1928_, v_mkInfoTree_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v_a_1935_, v___x_1942_);
lean_dec_ref(v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1951_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v_a_1937_);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1937_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_a_1937_);
v_a_1952_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_a_1962_ = lean_ctor_get(v_r_1936_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v_r_1936_);
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___lam__0(v___y_1928_, v_mkInfoTree_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v_a_1935_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1972_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v_a_1962_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1962_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_a_1962_);
v_a_1973_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1964_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg___boxed(lean_object* v_x_1981_, lean_object* v_mkInfoTree_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_1981_, v_mkInfoTree_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(lean_object* v_stx_1991_, lean_object* v_output_1992_, lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___f_2001_; lean_object* v___x_2002_; 
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2001_, 0, v_stx_1991_);
lean_closure_set(v___f_2001_, 1, v_output_1992_);
v___x_2002_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_1993_, v___f_2001_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg___boxed(lean_object* v_stx_2003_, lean_object* v_output_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_stx_2003_, v_output_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_beforeStx_2014_, lean_object* v_afterStx_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_inc_ref(v___y_2017_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2025_, 0, v_x_2016_);
lean_closure_set(v___f_2025_, 1, v___y_2017_);
lean_inc(v_afterStx_2015_);
lean_inc(v_beforeStx_2014_);
v___x_2026_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2026_, 0, lean_box(0));
lean_closure_set(v___x_2026_, 1, v_beforeStx_2014_);
lean_closure_set(v___x_2026_, 2, v_afterStx_2015_);
lean_closure_set(v___x_2026_, 3, v___f_2025_);
v___x_2027_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_beforeStx_2014_, v_afterStx_2015_, v___x_2026_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2027_) == 0)
{
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_beforeStx_2036_, lean_object* v_afterStx_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_beforeStx_2036_, v_afterStx_2037_, v_x_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1));
v___x_2051_ = l_String_toRawSubstring_x27(v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_a_2073_, lean_object* v_rhs_2074_, uint8_t v___x_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, uint8_t v___x_2080_, lean_object* v_body_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_ref_2090_; lean_object* v_quotContext_2091_; lean_object* v_currMacroScope_2092_; lean_object* v___x_2093_; 
v_ref_2090_ = lean_ctor_get(v___y_2087_, 5);
lean_inc(v_ref_2090_);
v_quotContext_2091_ = lean_ctor_get(v___y_2087_, 10);
v_currMacroScope_2092_ = lean_ctor_get(v___y_2087_, 11);
lean_inc_ref(v_a_2073_);
v___x_2093_ = l_Lean_Elab_Term_exprToSyntax(v_a_2073_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v_ref_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v_ref_2095_ = l_Lean_replaceRef(v_rhs_2074_, v_ref_2090_);
v___x_2096_ = l_Lean_SourceInfo_fromRef(v_ref_2095_, v___x_2075_);
lean_dec(v_ref_2095_);
v___x_2097_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0));
lean_inc(v___x_2096_);
v___x_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2);
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3));
lean_inc(v_currMacroScope_2092_);
lean_inc(v_quotContext_2091_);
v___x_2101_ = l_Lean_addMacroScope(v_quotContext_2091_, v___x_2100_, v_currMacroScope_2092_);
v___x_2102_ = lean_box(0);
lean_inc(v___x_2101_);
lean_inc(v___x_2096_);
v___x_2103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2096_);
lean_ctor_set(v___x_2103_, 1, v___x_2099_);
lean_ctor_set(v___x_2103_, 2, v___x_2101_);
lean_ctor_set(v___x_2103_, 3, v___x_2102_);
v___x_2104_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2105_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2104_);
v___x_2106_ = l_Lean_Syntax_node2(v___x_2096_, v___x_2105_, v___x_2098_, v___x_2103_);
v___x_2107_ = l_Lean_SourceInfo_fromRef(v_ref_2090_, v___x_2075_);
v___x_2108_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2109_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6));
lean_inc(v___x_2107_);
v___x_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2107_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_inc(v___x_2107_);
v___x_2112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2107_);
lean_ctor_set(v___x_2112_, 1, v___x_2097_);
lean_inc(v___x_2107_);
v___x_2113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2107_);
lean_ctor_set(v___x_2113_, 1, v___x_2099_);
lean_ctor_set(v___x_2113_, 2, v___x_2101_);
lean_ctor_set(v___x_2113_, 3, v___x_2102_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_2107_);
v___x_2115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2107_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_2107_);
v___x_2117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2107_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2119_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9));
lean_inc(v___x_2107_);
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2107_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2123_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2122_);
lean_inc(v___x_2107_);
v___x_2124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2107_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2126_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_2107_);
v___x_2127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2107_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2129_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2128_);
v___x_2130_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_2107_);
v___x_2131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2107_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
lean_inc(v___x_2107_);
v___x_2132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2107_);
lean_ctor_set(v___x_2132_, 1, v___x_2128_);
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2134_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2133_);
v___x_2135_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13));
lean_inc(v___x_2107_);
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2107_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2138_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
lean_inc(v___x_2107_);
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2107_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
lean_inc(v___x_2107_);
v___x_2141_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2138_, v___x_2140_);
lean_inc(v___x_2107_);
v___x_2142_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2141_);
v___x_2143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16));
lean_inc(v___x_2107_);
v___x_2144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2107_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
lean_inc_ref(v___x_2127_);
lean_inc(v___x_2107_);
v___x_2145_ = l_Lean_Syntax_node5(v___x_2107_, v___x_2134_, v___x_2136_, v___x_2142_, v___x_2127_, v___x_2144_, v_a_2094_);
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_2107_);
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2107_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
lean_inc_ref(v___x_2115_);
lean_inc(v___x_2107_);
v___x_2148_ = l_Lean_Syntax_node5(v___x_2107_, v___x_2129_, v___x_2131_, v___x_2132_, v___x_2115_, v___x_2145_, v___x_2147_);
lean_inc(v___x_2107_);
v___x_2149_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2151_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2150_);
lean_inc_ref(v___x_2127_);
lean_inc(v___x_2107_);
v___x_2152_ = l_Lean_Syntax_node2(v___x_2107_, v___x_2151_, v___x_2127_, v___x_2106_);
lean_inc(v___x_2107_);
v___x_2153_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2152_);
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
lean_inc(v___x_2107_);
v___x_2155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2107_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19));
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2076_);
v___x_2157_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20));
v___x_2159_ = l_Lean_Name_mkStr4(v___x_2076_, v___x_2077_, v___x_2078_, v___x_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_2107_);
v___x_2161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2107_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
lean_inc(v___x_2107_);
v___x_2162_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2079_);
lean_inc(v___x_2107_);
v___x_2163_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
lean_inc(v___x_2107_);
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2107_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v___x_2107_);
v___x_2166_ = l_Lean_Syntax_node4(v___x_2107_, v___x_2159_, v___x_2161_, v___x_2163_, v___x_2165_, v_body_2081_);
lean_inc(v___x_2107_);
v___x_2167_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2125_, v___x_2166_);
lean_inc(v___x_2107_);
v___x_2168_ = l_Lean_Syntax_node1(v___x_2107_, v___x_2157_, v___x_2167_);
lean_inc(v___x_2107_);
v___x_2169_ = l_Lean_Syntax_node6(v___x_2107_, v___x_2123_, v___x_2124_, v___x_2127_, v___x_2149_, v___x_2153_, v___x_2155_, v___x_2168_);
lean_inc_ref(v___x_2117_);
lean_inc_ref(v___x_2113_);
lean_inc_ref(v___x_2112_);
lean_inc(v___x_2107_);
v___x_2170_ = l_Lean_Syntax_node5(v___x_2107_, v___x_2119_, v___x_2121_, v___x_2112_, v___x_2113_, v___x_2117_, v___x_2169_);
v___x_2171_ = l_Lean_Syntax_node7(v___x_2107_, v___x_2109_, v___x_2111_, v___x_2112_, v___x_2113_, v___x_2115_, v_rhs_2074_, v___x_2117_, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2073_);
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_box(v___x_2080_);
lean_inc(v___x_2171_);
v___f_2175_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 12, 4);
lean_closure_set(v___f_2175_, 0, v___x_2171_);
lean_closure_set(v___f_2175_, 1, v___x_2172_);
lean_closure_set(v___f_2175_, 2, v___x_2174_);
lean_closure_set(v___f_2175_, 3, v___x_2173_);
v___x_2176_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_ref_2090_, v___x_2171_, v___f_2175_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec_ref(v___y_2087_);
return v___x_2176_;
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_ref_2090_);
lean_dec_ref(v___y_2087_);
lean_dec(v_body_2081_);
lean_dec(v___x_2079_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v___x_2077_);
lean_dec_ref(v___x_2076_);
lean_dec(v_rhs_2074_);
lean_dec_ref(v_a_2073_);
v_a_2177_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2093_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2093_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object** _args){
lean_object* v_a_2185_ = _args[0];
lean_object* v_rhs_2186_ = _args[1];
lean_object* v___x_2187_ = _args[2];
lean_object* v___x_2188_ = _args[3];
lean_object* v___x_2189_ = _args[4];
lean_object* v___x_2190_ = _args[5];
lean_object* v___x_2191_ = _args[6];
lean_object* v___x_2192_ = _args[7];
lean_object* v_body_2193_ = _args[8];
lean_object* v___y_2194_ = _args[9];
lean_object* v___y_2195_ = _args[10];
lean_object* v___y_2196_ = _args[11];
lean_object* v___y_2197_ = _args[12];
lean_object* v___y_2198_ = _args[13];
lean_object* v___y_2199_ = _args[14];
lean_object* v___y_2200_ = _args[15];
lean_object* v___y_2201_ = _args[16];
_start:
{
uint8_t v___x_75430__boxed_2202_; uint8_t v___x_75435__boxed_2203_; lean_object* v_res_2204_; 
v___x_75430__boxed_2202_ = lean_unbox(v___x_2187_);
v___x_75435__boxed_2203_ = lean_unbox(v___x_2192_);
v_res_2204_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_a_2185_, v_rhs_2186_, v___x_75430__boxed_2202_, v___x_2188_, v___x_2189_, v___x_2190_, v___x_2191_, v___x_75435__boxed_2203_, v_body_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0(lean_object* v___x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_quotContext_2209_; lean_object* v_currMacroScope_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_quotContext_2209_ = lean_ctor_get(v___y_2206_, 10);
lean_inc(v_quotContext_2209_);
v_currMacroScope_2210_ = lean_ctor_get(v___y_2206_, 11);
lean_inc(v_currMacroScope_2210_);
lean_dec_ref(v___y_2206_);
v___x_2211_ = l_Lean_addMacroScope(v_quotContext_2209_, v___x_2205_, v_currMacroScope_2210_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0___boxed(lean_object* v___x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___lam__0(v___x_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___f_2226_; lean_object* v___x_2227_; 
v___f_2226_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___closed__2));
v___x_2227_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2226_, v___y_2223_, v___y_2224_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg___boxed(lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_ref_2232_, uint8_t v_canonical_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2251_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2251_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2251_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = l_Lean_mkIdentFrom(v_ref_2232_, v_a_2243_, v_canonical_2233_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
v_a_2252_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2242_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2242_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_ref_2260_, lean_object* v_canonical_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
uint8_t v_canonical_boxed_2270_; lean_object* v_res_2271_; 
v_canonical_boxed_2270_ = lean_unbox(v_canonical_2261_);
v_res_2271_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_ref_2260_, v_canonical_boxed_2270_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v_ref_2260_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4(lean_object* v_env_2272_, lean_object* v_options_2273_, lean_object* v_currNamespace_2274_, lean_object* v_openDecls_2275_, lean_object* v_n_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = l_Lean_ResolveName_resolveGlobalName(v_env_2272_, v_options_2273_, v_currNamespace_2274_, v_openDecls_2275_, v_n_2276_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4___boxed(lean_object* v_env_2281_, lean_object* v_options_2282_, lean_object* v_currNamespace_2283_, lean_object* v_openDecls_2284_, lean_object* v_n_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4(v_env_2281_, v_options_2282_, v_currNamespace_2283_, v_openDecls_2284_, v_n_2285_, v___y_2286_, v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_options_2282_);
return v_res_2288_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l_Lean_maxRecDepthErrorMessage;
v___x_2295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__3);
v___x_2297_ = l_Lean_MessageData_ofFormat(v___x_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__4);
v___x_2299_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__2));
v___x_2300_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(lean_object* v_ref_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___closed__5);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v_ref_2301_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg___boxed(lean_object* v_ref_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_ref_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3(lean_object* v_currNamespace_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_currNamespace_2309_);
lean_ctor_set(v___x_2312_, 1, v___y_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3___boxed(lean_object* v_currNamespace_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3(v_currNamespace_2313_, v___y_2314_, v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2316_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2317_; double v___x_2318_; 
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_float_of_nat(v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_cls_2321_, lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_ref_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2374_; 
v_ref_2328_ = lean_ctor_get(v___y_2325_, 5);
v___x_2329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2374_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2374_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v_traceState_2335_; lean_object* v_env_2336_; lean_object* v_nextMacroScope_2337_; lean_object* v_ngen_2338_; lean_object* v_auxDeclNGen_2339_; lean_object* v_cache_2340_; lean_object* v_messages_2341_; lean_object* v_infoState_2342_; lean_object* v_snapshotTasks_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2373_; 
v___x_2334_ = lean_st_ref_take(v___y_2326_);
v_traceState_2335_ = lean_ctor_get(v___x_2334_, 4);
v_env_2336_ = lean_ctor_get(v___x_2334_, 0);
v_nextMacroScope_2337_ = lean_ctor_get(v___x_2334_, 1);
v_ngen_2338_ = lean_ctor_get(v___x_2334_, 2);
v_auxDeclNGen_2339_ = lean_ctor_get(v___x_2334_, 3);
v_cache_2340_ = lean_ctor_get(v___x_2334_, 5);
v_messages_2341_ = lean_ctor_get(v___x_2334_, 6);
v_infoState_2342_ = lean_ctor_get(v___x_2334_, 7);
v_snapshotTasks_2343_ = lean_ctor_get(v___x_2334_, 8);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2345_ = v___x_2334_;
v_isShared_2346_ = v_isSharedCheck_2373_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snapshotTasks_2343_);
lean_inc(v_infoState_2342_);
lean_inc(v_messages_2341_);
lean_inc(v_cache_2340_);
lean_inc(v_traceState_2335_);
lean_inc(v_auxDeclNGen_2339_);
lean_inc(v_ngen_2338_);
lean_inc(v_nextMacroScope_2337_);
lean_inc(v_env_2336_);
lean_dec(v___x_2334_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2373_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
uint64_t v_tid_2347_; lean_object* v_traces_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2372_; 
v_tid_2347_ = lean_ctor_get_uint64(v_traceState_2335_, sizeof(void*)*1);
v_traces_2348_ = lean_ctor_get(v_traceState_2335_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_traceState_2335_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2350_ = v_traceState_2335_;
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_traces_2348_);
lean_dec(v_traceState_2335_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; double v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__0);
v___x_2354_ = 0;
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2356_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2356_, 0, v_cls_2321_);
lean_ctor_set(v___x_2356_, 1, v___x_2352_);
lean_ctor_set(v___x_2356_, 2, v___x_2355_);
lean_ctor_set_float(v___x_2356_, sizeof(void*)*3, v___x_2353_);
lean_ctor_set_float(v___x_2356_, sizeof(void*)*3 + 8, v___x_2353_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*3 + 16, v___x_2354_);
v___x_2357_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___closed__1));
v___x_2358_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v_a_2330_);
lean_ctor_set(v___x_2358_, 2, v___x_2357_);
lean_inc(v_ref_2328_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v_ref_2328_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = l_Lean_PersistentArray_push___redArg(v_traces_2348_, v___x_2359_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2360_);
v___x_2362_ = v___x_2350_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2360_);
lean_ctor_set_uint64(v_reuseFailAlloc_2371_, sizeof(void*)*1, v_tid_2347_);
v___x_2362_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 4, v___x_2362_);
v___x_2364_ = v___x_2345_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_env_2336_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_nextMacroScope_2337_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_ngen_2338_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_auxDeclNGen_2339_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2370_, 5, v_cache_2340_);
lean_ctor_set(v_reuseFailAlloc_2370_, 6, v_messages_2341_);
lean_ctor_set(v_reuseFailAlloc_2370_, 7, v_infoState_2342_);
lean_ctor_set(v_reuseFailAlloc_2370_, 8, v_snapshotTasks_2343_);
v___x_2364_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2365_ = lean_st_ref_set(v___y_2326_, v___x_2364_);
v___x_2366_ = lean_box(0);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2366_);
v___x_2368_ = v___x_2332_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_cls_2375_, lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_2375_, v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(lean_object* v_keys_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_array_get_size(v_keys_2383_);
v___x_2387_ = lean_nat_dec_lt(v_i_2384_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_dec(v_i_2384_);
return v___x_2387_;
}
else
{
lean_object* v_k_x27_2388_; uint8_t v___x_2389_; 
v_k_x27_2388_ = lean_array_fget_borrowed(v_keys_2383_, v_i_2384_);
v___x_2389_ = l_Lean_instBEqExtraModUse_beq(v_k_2385_, v_k_x27_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(1u);
v___x_2391_ = lean_nat_add(v_i_2384_, v___x_2390_);
lean_dec(v_i_2384_);
v_i_2384_ = v___x_2391_;
goto _start;
}
else
{
lean_dec(v_i_2384_);
return v___x_2389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg___boxed(lean_object* v_keys_2393_, lean_object* v_i_2394_, lean_object* v_k_2395_){
_start:
{
uint8_t v_res_2396_; lean_object* v_r_2397_; 
v_res_2396_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_keys_2393_, v_i_2394_, v_k_2395_);
lean_dec_ref(v_k_2395_);
lean_dec_ref(v_keys_2393_);
v_r_2397_ = lean_box(v_res_2396_);
return v_r_2397_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(lean_object* v_x_2398_, size_t v_x_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 0)
{
lean_object* v_es_2401_; lean_object* v___x_2402_; size_t v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v_j_2406_; lean_object* v___x_2407_; 
v_es_2401_ = lean_ctor_get(v_x_2398_, 0);
lean_inc_ref(v_es_2401_);
lean_dec_ref(v_x_2398_);
v___x_2402_ = lean_box(2);
v___x_2403_ = ((size_t)5ULL);
v___x_2404_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2405_ = lean_usize_land(v_x_2399_, v___x_2404_);
v_j_2406_ = lean_usize_to_nat(v___x_2405_);
v___x_2407_ = lean_array_get(v___x_2402_, v_es_2401_, v_j_2406_);
lean_dec(v_j_2406_);
lean_dec_ref(v_es_2401_);
switch(lean_obj_tag(v___x_2407_))
{
case 0:
{
lean_object* v_key_2408_; uint8_t v___x_2409_; 
v_key_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_key_2408_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = l_Lean_instBEqExtraModUse_beq(v_x_2400_, v_key_2408_);
lean_dec(v_key_2408_);
return v___x_2409_;
}
case 1:
{
lean_object* v_node_2410_; size_t v___x_2411_; 
v_node_2410_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_node_2410_);
lean_dec_ref(v___x_2407_);
v___x_2411_ = lean_usize_shift_right(v_x_2399_, v___x_2403_);
v_x_2398_ = v_node_2410_;
v_x_2399_ = v___x_2411_;
goto _start;
}
default: 
{
uint8_t v___x_2413_; 
v___x_2413_ = 0;
return v___x_2413_;
}
}
}
else
{
lean_object* v_ks_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_ks_2414_ = lean_ctor_get(v_x_2398_, 0);
lean_inc_ref(v_ks_2414_);
lean_dec_ref(v_x_2398_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_ks_2414_, v___x_2415_, v_x_2400_);
lean_dec_ref(v_ks_2414_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg___boxed(lean_object* v_x_2417_, lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
size_t v_x_75966__boxed_2420_; uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_x_75966__boxed_2420_ = lean_unbox_usize(v_x_2418_);
lean_dec(v_x_2418_);
v_res_2421_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_2417_, v_x_75966__boxed_2420_, v_x_2419_);
lean_dec_ref(v_x_2419_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
uint64_t v___x_2425_; size_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2425_ = l_Lean_instHashableExtraModUse_hash(v_x_2424_);
v___x_2426_ = lean_uint64_to_usize(v___x_2425_);
v___x_2427_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_2423_, v___x_2426_, v_x_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg___boxed(lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
uint8_t v_res_2430_; lean_object* v_r_2431_; 
v_res_2430_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v_x_2428_, v_x_2429_);
lean_dec_ref(v_x_2429_);
v_r_2431_ = lean_box(v_res_2430_);
return v_r_2431_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__1));
v___x_2435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__0));
v___x_2436_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3(void){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__3);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__4);
v___x_2443_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
lean_ctor_set(v___x_2443_, 2, v___x_2442_);
lean_ctor_set(v___x_2443_, 3, v___x_2442_);
lean_ctor_set(v___x_2443_, 4, v___x_2442_);
lean_ctor_set(v___x_2443_, 5, v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__9));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__11));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__14));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__16));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(lean_object* v_mod_2465_, uint8_t v_isMeta_2466_, lean_object* v_hint_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v_env_2477_; uint8_t v_isExporting_2478_; lean_object* v___x_2479_; lean_object* v_env_2480_; lean_object* v___x_2481_; lean_object* v_entry_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2476_ = lean_st_ref_get(v___y_2474_);
v_env_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_env_2477_);
lean_dec(v___x_2476_);
v_isExporting_2478_ = lean_ctor_get_uint8(v_env_2477_, sizeof(void*)*8);
lean_dec_ref(v_env_2477_);
v___x_2479_ = lean_st_ref_get(v___y_2474_);
v_env_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2480_);
lean_dec(v___x_2479_);
v___x_2481_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__2);
lean_inc(v_mod_2465_);
v_entry_2482_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2482_, 0, v_mod_2465_);
lean_ctor_set_uint8(v_entry_2482_, sizeof(void*)*1, v_isExporting_2478_);
lean_ctor_set_uint8(v_entry_2482_, sizeof(void*)*1 + 1, v_isMeta_2466_);
v___x_2483_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2484_ = lean_box(1);
v___x_2485_ = lean_box(0);
v___x_2528_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2481_, v___x_2483_, v_env_2480_, v___x_2484_, v___x_2485_);
v___x_2529_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v___x_2528_, v_entry_2482_);
if (v___x_2529_ == 0)
{
lean_object* v_cls_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___x_2552_; 
v_cls_2530_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__8));
v___x_2531_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_2530_, v___y_2473_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2531_);
v___x_2552_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
if (v___x_2552_ == 0)
{
lean_dec(v_hint_2467_);
lean_dec(v_mod_2465_);
v___y_2487_ = v___y_2472_;
v___y_2488_ = v___y_2474_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2553_; lean_object* v___y_2555_; 
v___x_2553_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__15);
if (v_isExporting_2478_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__20));
v___y_2555_ = v___x_2562_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__21));
v___y_2555_ = v___x_2563_;
goto v___jp_2554_;
}
v___jp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = l_Lean_stringToMessageData(v___y_2555_);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2553_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__17);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
if (v_isMeta_2466_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__18));
v___y_2539_ = v___x_2559_;
v___y_2540_ = v___x_2560_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__19));
v___y_2539_ = v___x_2559_;
v___y_2540_ = v___x_2561_;
goto v___jp_2538_;
}
}
}
v___jp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2534_);
lean_ctor_set(v___x_2536_, 1, v___y_2535_);
v___x_2537_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_2530_, v___x_2536_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref(v___x_2537_);
v___y_2487_ = v___y_2472_;
v___y_2488_ = v___y_2474_;
goto v___jp_2486_;
}
else
{
lean_dec_ref(v_entry_2482_);
return v___x_2537_;
}
}
v___jp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2541_ = l_Lean_stringToMessageData(v___y_2540_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___y_2539_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__10);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_MessageData_ofName(v_mod_2465_);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = l_Lean_Name_isAnonymous(v_hint_2467_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__12);
v___x_2549_ = l_Lean_MessageData_ofName(v_hint_2467_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___y_2534_ = v___x_2546_;
v___y_2535_ = v___x_2550_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2551_; 
lean_dec(v_hint_2467_);
v___x_2551_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__13);
v___y_2534_ = v___x_2546_;
v___y_2535_ = v___x_2551_;
goto v___jp_2533_;
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v_entry_2482_);
lean_dec(v_hint_2467_);
lean_dec(v_mod_2465_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
v___jp_2486_:
{
lean_object* v___x_2489_; lean_object* v_toEnvExtension_2490_; lean_object* v_env_2491_; lean_object* v_nextMacroScope_2492_; lean_object* v_ngen_2493_; lean_object* v_auxDeclNGen_2494_; lean_object* v_traceState_2495_; lean_object* v_messages_2496_; lean_object* v_infoState_2497_; lean_object* v_snapshotTasks_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2526_; 
v___x_2489_ = lean_st_ref_take(v___y_2488_);
v_toEnvExtension_2490_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_toEnvExtension_2490_);
v_env_2491_ = lean_ctor_get(v___x_2489_, 0);
v_nextMacroScope_2492_ = lean_ctor_get(v___x_2489_, 1);
v_ngen_2493_ = lean_ctor_get(v___x_2489_, 2);
v_auxDeclNGen_2494_ = lean_ctor_get(v___x_2489_, 3);
v_traceState_2495_ = lean_ctor_get(v___x_2489_, 4);
v_messages_2496_ = lean_ctor_get(v___x_2489_, 6);
v_infoState_2497_ = lean_ctor_get(v___x_2489_, 7);
v_snapshotTasks_2498_ = lean_ctor_get(v___x_2489_, 8);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2489_, 5);
lean_dec(v_unused_2527_);
v___x_2500_ = v___x_2489_;
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snapshotTasks_2498_);
lean_inc(v_infoState_2497_);
lean_inc(v_messages_2496_);
lean_inc(v_traceState_2495_);
lean_inc(v_auxDeclNGen_2494_);
lean_inc(v_ngen_2493_);
lean_inc(v_nextMacroScope_2492_);
lean_inc(v_env_2491_);
lean_dec(v___x_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_asyncMode_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v_asyncMode_2502_ = lean_ctor_get(v_toEnvExtension_2490_, 2);
lean_inc(v_asyncMode_2502_);
lean_dec_ref(v_toEnvExtension_2490_);
v___x_2503_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2483_, v_env_2491_, v_entry_2482_, v_asyncMode_2502_, v___x_2485_);
lean_dec(v_asyncMode_2502_);
v___x_2504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__5);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 5, v___x_2504_);
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2506_ = v___x_2500_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_nextMacroScope_2492_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_ngen_2493_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_auxDeclNGen_2494_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_traceState_2495_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_messages_2496_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_infoState_2497_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_snapshotTasks_2498_);
v___x_2506_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_mctx_2509_; lean_object* v_zetaDeltaFVarIds_2510_; lean_object* v_postponed_2511_; lean_object* v_diag_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2523_; 
v___x_2507_ = lean_st_ref_set(v___y_2488_, v___x_2506_);
v___x_2508_ = lean_st_ref_take(v___y_2487_);
v_mctx_2509_ = lean_ctor_get(v___x_2508_, 0);
v_zetaDeltaFVarIds_2510_ = lean_ctor_get(v___x_2508_, 2);
v_postponed_2511_ = lean_ctor_get(v___x_2508_, 3);
v_diag_2512_ = lean_ctor_get(v___x_2508_, 4);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2508_, 1);
lean_dec(v_unused_2524_);
v___x_2514_ = v___x_2508_;
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_diag_2512_);
lean_inc(v_postponed_2511_);
lean_inc(v_zetaDeltaFVarIds_2510_);
lean_inc(v_mctx_2509_);
lean_dec(v___x_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2523_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___closed__6);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_mctx_2509_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_zetaDeltaFVarIds_2510_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_postponed_2511_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_diag_2512_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_st_ref_set(v___y_2487_, v___x_2518_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18___boxed(lean_object* v_mod_2566_, lean_object* v_isMeta_2567_, lean_object* v_hint_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v_isMeta_boxed_2577_; lean_object* v_res_2578_; 
v_isMeta_boxed_2577_ = lean_unbox(v_isMeta_2567_);
v_res_2578_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_mod_2566_, v_isMeta_boxed_2577_, v_hint_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(lean_object* v___x_2579_, lean_object* v_declName_2580_, lean_object* v_as_2581_, size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_lt(v_i_2583_, v_sz_2582_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_dec(v_declName_2580_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_b_2584_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v_modules_2596_; lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v_toImport_2600_; lean_object* v_module_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2595_ = l_Lean_Environment_header(v___x_2579_);
v_modules_2596_ = lean_ctor_get(v___x_2595_, 3);
lean_inc_ref(v_modules_2596_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2598_ = lean_array_uget_borrowed(v_as_2581_, v_i_2583_);
v___x_2599_ = lean_array_get(v___x_2597_, v_modules_2596_, v_a_2598_);
lean_dec_ref(v_modules_2596_);
v_toImport_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc_ref(v_toImport_2600_);
lean_dec(v___x_2599_);
v_module_2601_ = lean_ctor_get(v_toImport_2600_, 0);
lean_inc(v_module_2601_);
lean_dec_ref(v_toImport_2600_);
v___x_2602_ = 0;
lean_inc(v_declName_2580_);
v___x_2603_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_module_2601_, v___x_2602_, v_declName_2580_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; 
lean_dec_ref(v___x_2603_);
v___x_2604_ = lean_box(0);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_add(v_i_2583_, v___x_2605_);
v_i_2583_ = v___x_2606_;
v_b_2584_ = v___x_2604_;
goto _start;
}
else
{
lean_dec(v_declName_2580_);
return v___x_2603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19___boxed(lean_object* v___x_2608_, lean_object* v_declName_2609_, lean_object* v_as_2610_, lean_object* v_sz_2611_, lean_object* v_i_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
size_t v_sz_boxed_2622_; size_t v_i_boxed_2623_; lean_object* v_res_2624_; 
v_sz_boxed_2622_ = lean_unbox_usize(v_sz_2611_);
lean_dec(v_sz_2611_);
v_i_boxed_2623_ = lean_unbox_usize(v_i_2612_);
lean_dec(v_i_2612_);
v_res_2624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(v___x_2608_, v_declName_2609_, v_as_2610_, v_sz_boxed_2622_, v_i_boxed_2623_, v_b_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v_as_2610_);
lean_dec_ref(v___x_2608_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__1));
v___x_2628_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__0));
v___x_2629_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(lean_object* v_declName_2632_, uint8_t v_isMeta_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; lean_object* v_env_2646_; lean_object* v___y_2648_; lean_object* v___x_2661_; 
v___x_2642_ = lean_st_ref_get(v___y_2640_);
v_env_2646_ = lean_ctor_get(v___x_2642_, 0);
lean_inc_ref(v_env_2646_);
lean_dec(v___x_2642_);
v___x_2661_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2646_, v_declName_2632_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref(v_env_2646_);
lean_dec(v_declName_2632_);
goto v___jp_2643_;
}
else
{
lean_object* v_val_2662_; lean_object* v___x_2663_; lean_object* v_modules_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref(v___x_2661_);
v___x_2663_ = l_Lean_Environment_header(v_env_2646_);
v_modules_2664_ = lean_ctor_get(v___x_2663_, 3);
lean_inc_ref(v_modules_2664_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = lean_array_get_size(v_modules_2664_);
v___x_2666_ = lean_nat_dec_lt(v_val_2662_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v_modules_2664_);
lean_dec(v_val_2662_);
lean_dec_ref(v_env_2646_);
lean_dec(v_declName_2632_);
goto v___jp_2643_;
}
else
{
lean_object* v___x_2667_; lean_object* v_env_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___y_2672_; 
v___x_2667_ = lean_st_ref_get(v___y_2640_);
v_env_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref(v_env_2668_);
lean_dec(v___x_2667_);
v___x_2669_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__2);
v___x_2670_ = lean_array_fget(v_modules_2664_, v_val_2662_);
lean_dec(v_val_2662_);
lean_dec_ref(v_modules_2664_);
if (v_isMeta_2633_ == 0)
{
lean_dec_ref(v_env_2668_);
v___y_2672_ = v_isMeta_2633_;
goto v___jp_2671_;
}
else
{
uint8_t v___x_2683_; 
lean_inc(v_declName_2632_);
v___x_2683_ = l_Lean_isMarkedMeta(v_env_2668_, v_declName_2632_);
if (v___x_2683_ == 0)
{
v___y_2672_ = v_isMeta_2633_;
goto v___jp_2671_;
}
else
{
uint8_t v___x_2684_; 
v___x_2684_ = 0;
v___y_2672_ = v___x_2684_;
goto v___jp_2671_;
}
}
v___jp_2671_:
{
lean_object* v_toImport_2673_; lean_object* v_module_2674_; lean_object* v___x_2675_; 
v_toImport_2673_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref(v_toImport_2673_);
lean_dec(v___x_2670_);
v_module_2674_ = lean_ctor_get(v_toImport_2673_, 0);
lean_inc(v_module_2674_);
lean_dec_ref(v_toImport_2673_);
lean_inc(v_declName_2632_);
v___x_2675_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18(v_module_2674_, v___y_2672_, v_declName_2632_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref(v___x_2675_);
v___x_2676_ = l_Lean_indirectModUseExt;
v___x_2677_ = lean_box(1);
v___x_2678_ = lean_box(0);
lean_inc_ref(v_env_2646_);
v___x_2679_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2669_, v___x_2676_, v_env_2646_, v___x_2677_, v___x_2678_);
v___x_2680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_2679_, v_declName_2632_);
lean_dec(v___x_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; 
v___x_2681_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___closed__3));
v___y_2648_ = v___x_2681_;
goto v___jp_2647_;
}
else
{
lean_object* v_val_2682_; 
v_val_2682_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_val_2682_);
lean_dec_ref(v___x_2680_);
v___y_2648_ = v_val_2682_;
goto v___jp_2647_;
}
}
else
{
lean_dec_ref(v_env_2646_);
lean_dec(v_declName_2632_);
return v___x_2675_;
}
}
}
}
v___jp_2643_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; size_t v_sz_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2649_ = lean_box(0);
v_sz_2650_ = lean_array_size(v___y_2648_);
v___x_2651_ = ((size_t)0ULL);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__19(v_env_2646_, v_declName_2632_, v___y_2648_, v_sz_2650_, v___x_2651_, v___x_2649_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v_env_2646_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; 
v_unused_2660_ = lean_ctor_get(v___x_2652_, 0);
lean_dec(v_unused_2660_);
v___x_2654_ = v___x_2652_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_dec(v___x_2652_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2649_);
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2649_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
return v___x_2652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14___boxed(lean_object* v_declName_2685_, lean_object* v_isMeta_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
uint8_t v_isMeta_boxed_2695_; lean_object* v_res_2696_; 
v_isMeta_boxed_2695_ = lean_unbox(v_isMeta_2686_);
v_res_2696_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(v_declName_2685_, v_isMeta_boxed_2695_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(lean_object* v_as_x27_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
if (lean_obj_tag(v_as_x27_2697_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_b_2698_);
return v___x_2707_;
}
else
{
lean_object* v_head_2708_; lean_object* v_tail_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
v_head_2708_ = lean_ctor_get(v_as_x27_2697_, 0);
lean_inc(v_head_2708_);
v_tail_2709_ = lean_ctor_get(v_as_x27_2697_, 1);
lean_inc(v_tail_2709_);
lean_dec_ref(v_as_x27_2697_);
v___x_2710_ = 1;
v___x_2711_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14(v_head_2708_, v___x_2710_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v___x_2712_; 
lean_dec_ref(v___x_2711_);
v___x_2712_ = lean_box(0);
v_as_x27_2697_ = v_tail_2709_;
v_b_2698_ = v___x_2712_;
goto _start;
}
else
{
lean_dec(v_tail_2709_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg___boxed(lean_object* v_as_x27_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_as_x27_2714_, v_b_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(lean_object* v_x_2725_, lean_object* v___y_2726_){
_start:
{
if (lean_obj_tag(v_x_2725_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2727_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_a_2727_);
v___x_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_a_2727_);
lean_ctor_set(v___x_2728_, 1, v___y_2726_);
return v___x_2728_;
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_a_2729_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2729_);
lean_ctor_set(v___x_2730_, 1, v___y_2726_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg___boxed(lean_object* v_x_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v_x_2731_, v___y_2732_);
lean_dec_ref(v_x_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0(lean_object* v_env_2734_, lean_object* v_stx_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2734_, v_stx_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
if (lean_obj_tag(v_a_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2748_; 
v_a_2740_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2738_, 0);
lean_dec(v_unused_2749_);
v___x_2742_ = v___x_2738_;
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2738_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2748_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2744_ = lean_box(0);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2744_);
v___x_2746_ = v___x_2742_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_a_2740_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2778_; 
v_val_2750_ = lean_ctor_get(v_a_2739_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2752_ = v_a_2739_;
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v_a_2739_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_snd_2754_; 
v_snd_2754_ = lean_ctor_get(v_val_2750_, 1);
lean_inc(v_snd_2754_);
lean_dec(v_val_2750_);
if (lean_obj_tag(v_snd_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2764_; 
lean_del_object(v___x_2752_);
v_a_2755_ = lean_ctor_get(v___x_2738_, 1);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2738_);
v_a_2756_ = lean_ctor_get(v_snd_2754_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_snd_2754_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2758_ = v_snd_2754_;
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v_snd_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v___x_2761_, v_a_2755_);
lean_dec_ref(v___x_2761_);
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2777_; 
v_a_2765_ = lean_ctor_get(v___x_2738_, 1);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2738_);
v_a_2766_ = lean_ctor_get(v_snd_2754_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_snd_2754_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2768_ = v_snd_2754_;
v_isShared_2769_ = v_isSharedCheck_2777_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v_snd_2754_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2777_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v_a_2766_);
v___x_2771_ = v___x_2752_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v___x_2773_, v_a_2765_);
lean_dec_ref(v___x_2773_);
return v___x_2774_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_a_2779_ = lean_ctor_get(v___x_2738_, 0);
v_a_2780_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2738_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_inc(v_a_2779_);
lean_dec(v___x_2738_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2779_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0___boxed(lean_object* v_env_2788_, lean_object* v_stx_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0(v_env_2788_, v_stx_2789_, v___y_2790_, v___y_2791_);
lean_dec_ref(v___y_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2(lean_object* v_env_2793_, lean_object* v_currNamespace_2794_, lean_object* v_openDecls_2795_, lean_object* v_n_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = l_Lean_ResolveName_resolveNamespace(v_env_2793_, v_currNamespace_2794_, v_openDecls_2795_, v_n_2796_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___y_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2___boxed(lean_object* v_env_2801_, lean_object* v_currNamespace_2802_, lean_object* v_openDecls_2803_, lean_object* v_n_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2(v_env_2801_, v_currNamespace_2802_, v_openDecls_2803_, v_n_2804_, v___y_2805_, v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(lean_object* v_msg_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_ref_2814_; lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
v_ref_2814_ = lean_ctor_get(v___y_2811_, 5);
v___x_2815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_inc(v_ref_2814_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_ref_2814_);
lean_ctor_set(v___x_2820_, 1, v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 1);
lean_ctor_set(v___x_2818_, 0, v___x_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg___boxed(lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(lean_object* v_ref_2832_, lean_object* v_msg_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_fileName_2842_; lean_object* v_fileMap_2843_; lean_object* v_options_2844_; lean_object* v_currRecDepth_2845_; lean_object* v_maxRecDepth_2846_; lean_object* v_ref_2847_; lean_object* v_currNamespace_2848_; lean_object* v_openDecls_2849_; lean_object* v_initHeartbeats_2850_; lean_object* v_maxHeartbeats_2851_; lean_object* v_quotContext_2852_; lean_object* v_currMacroScope_2853_; uint8_t v_diag_2854_; lean_object* v_cancelTk_x3f_2855_; uint8_t v_suppressElabErrors_2856_; lean_object* v_inheritedTraceOptions_2857_; lean_object* v_ref_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_fileName_2842_ = lean_ctor_get(v___y_2839_, 0);
v_fileMap_2843_ = lean_ctor_get(v___y_2839_, 1);
v_options_2844_ = lean_ctor_get(v___y_2839_, 2);
v_currRecDepth_2845_ = lean_ctor_get(v___y_2839_, 3);
v_maxRecDepth_2846_ = lean_ctor_get(v___y_2839_, 4);
v_ref_2847_ = lean_ctor_get(v___y_2839_, 5);
v_currNamespace_2848_ = lean_ctor_get(v___y_2839_, 6);
v_openDecls_2849_ = lean_ctor_get(v___y_2839_, 7);
v_initHeartbeats_2850_ = lean_ctor_get(v___y_2839_, 8);
v_maxHeartbeats_2851_ = lean_ctor_get(v___y_2839_, 9);
v_quotContext_2852_ = lean_ctor_get(v___y_2839_, 10);
v_currMacroScope_2853_ = lean_ctor_get(v___y_2839_, 11);
v_diag_2854_ = lean_ctor_get_uint8(v___y_2839_, sizeof(void*)*14);
v_cancelTk_x3f_2855_ = lean_ctor_get(v___y_2839_, 12);
v_suppressElabErrors_2856_ = lean_ctor_get_uint8(v___y_2839_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2857_ = lean_ctor_get(v___y_2839_, 13);
v_ref_2858_ = l_Lean_replaceRef(v_ref_2832_, v_ref_2847_);
lean_inc_ref(v_inheritedTraceOptions_2857_);
lean_inc(v_cancelTk_x3f_2855_);
lean_inc(v_currMacroScope_2853_);
lean_inc(v_quotContext_2852_);
lean_inc(v_maxHeartbeats_2851_);
lean_inc(v_initHeartbeats_2850_);
lean_inc(v_openDecls_2849_);
lean_inc(v_currNamespace_2848_);
lean_inc(v_maxRecDepth_2846_);
lean_inc(v_currRecDepth_2845_);
lean_inc_ref(v_options_2844_);
lean_inc_ref(v_fileMap_2843_);
lean_inc_ref(v_fileName_2842_);
v___x_2859_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2859_, 0, v_fileName_2842_);
lean_ctor_set(v___x_2859_, 1, v_fileMap_2843_);
lean_ctor_set(v___x_2859_, 2, v_options_2844_);
lean_ctor_set(v___x_2859_, 3, v_currRecDepth_2845_);
lean_ctor_set(v___x_2859_, 4, v_maxRecDepth_2846_);
lean_ctor_set(v___x_2859_, 5, v_ref_2858_);
lean_ctor_set(v___x_2859_, 6, v_currNamespace_2848_);
lean_ctor_set(v___x_2859_, 7, v_openDecls_2849_);
lean_ctor_set(v___x_2859_, 8, v_initHeartbeats_2850_);
lean_ctor_set(v___x_2859_, 9, v_maxHeartbeats_2851_);
lean_ctor_set(v___x_2859_, 10, v_quotContext_2852_);
lean_ctor_set(v___x_2859_, 11, v_currMacroScope_2853_);
lean_ctor_set(v___x_2859_, 12, v_cancelTk_x3f_2855_);
lean_ctor_set(v___x_2859_, 13, v_inheritedTraceOptions_2857_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*14, v_diag_2854_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*14 + 1, v_suppressElabErrors_2856_);
v___x_2860_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_2833_, v___y_2837_, v___y_2838_, v___x_2859_, v___y_2840_);
lean_dec_ref(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg___boxed(lean_object* v_ref_2861_, lean_object* v_msg_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_ref_2861_, v_msg_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v_ref_2861_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(lean_object* v_as_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
if (lean_obj_tag(v_as_2872_) == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
else
{
lean_object* v_head_2883_; lean_object* v_tail_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___x_2887_; lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2900_; 
v_head_2883_ = lean_ctor_get(v_as_2872_, 0);
lean_inc(v_head_2883_);
v_tail_2884_ = lean_ctor_get(v_as_2872_, 1);
lean_inc(v_tail_2884_);
lean_dec_ref(v_as_2872_);
v_fst_2885_ = lean_ctor_get(v_head_2883_, 0);
lean_inc(v_fst_2885_);
v_snd_2886_ = lean_ctor_get(v_head_2883_, 1);
lean_inc(v_snd_2886_);
lean_dec(v_head_2883_);
lean_inc(v_fst_2885_);
v___x_2887_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_2885_, v___y_2878_);
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2900_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2900_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_unbox(v_a_2888_);
lean_dec(v_a_2888_);
if (v___x_2892_ == 0)
{
lean_del_object(v___x_2890_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
v_as_2872_ = v_tail_2884_;
goto _start;
}
else
{
lean_object* v___x_2895_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 3);
lean_ctor_set(v___x_2890_, 0, v_snd_2886_);
v___x_2895_ = v___x_2890_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_snd_2886_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = l_Lean_MessageData_ofFormat(v___x_2895_);
v___x_2897_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_fst_2885_, v___x_2896_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref(v___x_2897_);
v_as_2872_ = v_tail_2884_;
goto _start;
}
else
{
lean_dec(v_tail_2884_);
return v___x_2897_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16___boxed(lean_object* v_as_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(v_as_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1(lean_object* v_env_2911_, lean_object* v_declName_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2915_; lean_object* v_env_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; uint8_t v___x_2919_; 
v___x_2915_ = 0;
v_env_2916_ = l_Lean_Environment_setExporting(v_env_2911_, v___x_2915_);
lean_inc(v_declName_2912_);
v___x_2917_ = l_Lean_mkPrivateName(v_env_2916_, v_declName_2912_);
v___x_2918_ = 1;
lean_inc_ref(v_env_2916_);
v___x_2919_ = l_Lean_Environment_contains(v_env_2916_, v___x_2917_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = l_Lean_privateToUserName(v_declName_2912_);
v___x_2921_ = l_Lean_Environment_contains(v_env_2916_, v___x_2920_, v___x_2918_);
v___x_2922_ = lean_box(v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___y_2914_);
return v___x_2923_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec_ref(v_env_2916_);
lean_dec(v_declName_2912_);
v___x_2924_ = lean_box(v___x_2919_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___y_2914_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1___boxed(lean_object* v_env_2926_, lean_object* v_declName_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1(v_env_2926_, v_declName_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v_env_2942_; lean_object* v_options_2943_; lean_object* v_currRecDepth_2944_; lean_object* v_maxRecDepth_2945_; lean_object* v_ref_2946_; lean_object* v_currNamespace_2947_; lean_object* v_openDecls_2948_; lean_object* v_quotContext_2949_; lean_object* v_currMacroScope_2950_; lean_object* v___x_2951_; lean_object* v_nextMacroScope_2952_; lean_object* v___f_2953_; lean_object* v___f_2954_; lean_object* v___f_2955_; lean_object* v___f_2956_; lean_object* v___f_2957_; lean_object* v_methods_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2941_ = lean_st_ref_get(v___y_2939_);
v_env_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_ref(v_env_2942_);
lean_dec(v___x_2941_);
v_options_2943_ = lean_ctor_get(v___y_2938_, 2);
v_currRecDepth_2944_ = lean_ctor_get(v___y_2938_, 3);
v_maxRecDepth_2945_ = lean_ctor_get(v___y_2938_, 4);
v_ref_2946_ = lean_ctor_get(v___y_2938_, 5);
v_currNamespace_2947_ = lean_ctor_get(v___y_2938_, 6);
v_openDecls_2948_ = lean_ctor_get(v___y_2938_, 7);
v_quotContext_2949_ = lean_ctor_get(v___y_2938_, 10);
v_currMacroScope_2950_ = lean_ctor_get(v___y_2938_, 11);
v___x_2951_ = lean_st_ref_get(v___y_2939_);
v_nextMacroScope_2952_ = lean_ctor_get(v___x_2951_, 1);
lean_inc(v_nextMacroScope_2952_);
lean_dec(v___x_2951_);
lean_inc_ref(v_env_2942_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2953_, 0, v_env_2942_);
lean_inc_ref(v_env_2942_);
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2954_, 0, v_env_2942_);
lean_inc(v_openDecls_2948_);
lean_inc(v_currNamespace_2947_);
lean_inc_ref(v_env_2942_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2955_, 0, v_env_2942_);
lean_closure_set(v___f_2955_, 1, v_currNamespace_2947_);
lean_closure_set(v___f_2955_, 2, v_openDecls_2948_);
lean_inc(v_currNamespace_2947_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2956_, 0, v_currNamespace_2947_);
lean_inc(v_openDecls_2948_);
lean_inc(v_currNamespace_2947_);
lean_inc_ref(v_options_2943_);
v___f_2957_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2957_, 0, v_env_2942_);
lean_closure_set(v___f_2957_, 1, v_options_2943_);
lean_closure_set(v___f_2957_, 2, v_currNamespace_2947_);
lean_closure_set(v___f_2957_, 3, v_openDecls_2948_);
v_methods_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2958_, 0, v___f_2953_);
lean_ctor_set(v_methods_2958_, 1, v___f_2956_);
lean_ctor_set(v_methods_2958_, 2, v___f_2954_);
lean_ctor_set(v_methods_2958_, 3, v___f_2955_);
lean_ctor_set(v_methods_2958_, 4, v___f_2957_);
lean_inc(v_ref_2946_);
lean_inc(v_maxRecDepth_2945_);
lean_inc(v_currRecDepth_2944_);
lean_inc(v_currMacroScope_2950_);
lean_inc(v_quotContext_2949_);
v___x_2959_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2959_, 0, v_methods_2958_);
lean_ctor_set(v___x_2959_, 1, v_quotContext_2949_);
lean_ctor_set(v___x_2959_, 2, v_currMacroScope_2950_);
lean_ctor_set(v___x_2959_, 3, v_currRecDepth_2944_);
lean_ctor_set(v___x_2959_, 4, v_maxRecDepth_2945_);
lean_ctor_set(v___x_2959_, 5, v_ref_2946_);
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2961_, 0, v_nextMacroScope_2952_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
lean_ctor_set(v___x_2961_, 2, v___x_2960_);
v___x_2962_ = lean_apply_2(v_x_2932_, v___x_2959_, v___x_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v_a_2964_; lean_object* v_macroScope_2965_; lean_object* v_traceMsgs_2966_; lean_object* v_expandedMacroDecls_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 1);
lean_inc(v_a_2963_);
v_a_2964_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2962_);
v_macroScope_2965_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_macroScope_2965_);
v_traceMsgs_2966_ = lean_ctor_get(v_a_2963_, 1);
lean_inc(v_traceMsgs_2966_);
v_expandedMacroDecls_2967_ = lean_ctor_get(v_a_2963_, 2);
lean_inc(v_expandedMacroDecls_2967_);
lean_dec(v_a_2963_);
v___x_2968_ = lean_box(0);
v___x_2969_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_expandedMacroDecls_2967_, v___x_2968_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v_env_2971_; lean_object* v_ngen_2972_; lean_object* v_auxDeclNGen_2973_; lean_object* v_traceState_2974_; lean_object* v_cache_2975_; lean_object* v_messages_2976_; lean_object* v_infoState_2977_; lean_object* v_snapshotTasks_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v___x_2969_);
v___x_2970_ = lean_st_ref_take(v___y_2939_);
v_env_2971_ = lean_ctor_get(v___x_2970_, 0);
v_ngen_2972_ = lean_ctor_get(v___x_2970_, 2);
v_auxDeclNGen_2973_ = lean_ctor_get(v___x_2970_, 3);
v_traceState_2974_ = lean_ctor_get(v___x_2970_, 4);
v_cache_2975_ = lean_ctor_get(v___x_2970_, 5);
v_messages_2976_ = lean_ctor_get(v___x_2970_, 6);
v_infoState_2977_ = lean_ctor_get(v___x_2970_, 7);
v_snapshotTasks_2978_ = lean_ctor_get(v___x_2970_, 8);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v___x_2970_, 1);
lean_dec(v_unused_3005_);
v___x_2980_ = v___x_2970_;
v_isShared_2981_ = v_isSharedCheck_3004_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_snapshotTasks_2978_);
lean_inc(v_infoState_2977_);
lean_inc(v_messages_2976_);
lean_inc(v_cache_2975_);
lean_inc(v_traceState_2974_);
lean_inc(v_auxDeclNGen_2973_);
lean_inc(v_ngen_2972_);
lean_inc(v_env_2971_);
lean_dec(v___x_2970_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3004_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 1, v_macroScope_2965_);
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_env_2971_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_macroScope_2965_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_ngen_2972_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_auxDeclNGen_2973_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_traceState_2974_);
lean_ctor_set(v_reuseFailAlloc_3003_, 5, v_cache_2975_);
lean_ctor_set(v_reuseFailAlloc_3003_, 6, v_messages_2976_);
lean_ctor_set(v_reuseFailAlloc_3003_, 7, v_infoState_2977_);
lean_ctor_set(v_reuseFailAlloc_3003_, 8, v_snapshotTasks_2978_);
v___x_2983_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_st_ref_set(v___y_2939_, v___x_2983_);
v___x_2985_ = l_List_reverse___redArg(v_traceMsgs_2966_);
v___x_2986_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__16(v___x_2985_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec_ref(v___y_2938_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v___x_2986_, 0);
lean_dec(v_unused_2994_);
v___x_2988_ = v___x_2986_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_dec(v___x_2986_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v_a_2964_);
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2964_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_a_2964_);
v_a_2995_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2986_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2986_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_traceMsgs_2966_);
lean_dec(v_macroScope_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v___y_2938_);
v_a_3006_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2969_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2969_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; 
v_a_3014_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_2962_);
if (lean_obj_tag(v_a_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v_a_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_a_3015_ = lean_ctor_get(v_a_3014_, 0);
lean_inc(v_a_3015_);
v_a_3016_ = lean_ctor_get(v_a_3014_, 1);
lean_inc_ref(v_a_3016_);
lean_dec_ref(v_a_3014_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___closed__0));
v___x_3018_ = lean_string_dec_eq(v_a_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3016_);
v___x_3020_ = l_Lean_MessageData_ofFormat(v___x_3019_);
v___x_3021_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_a_3015_, v___x_3020_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_a_3015_);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; 
lean_dec_ref(v_a_3016_);
lean_dec_ref(v___y_2938_);
v___x_3022_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_a_3015_);
return v___x_3022_;
}
}
else
{
lean_object* v___x_3023_; 
lean_dec_ref(v___y_2938_);
v___x_3023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg___boxed(lean_object* v_x_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v_x_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__5(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__4));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__7(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__6));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__9(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__8));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_letOrReassign_3054_, lean_object* v_decl_3055_, lean_object* v_dec_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_letOrReassign_3054_, v_decl_3055_, v_dec_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_letOrReassign_3066_, lean_object* v_decl_3067_, lean_object* v_dec_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3077_; 
lean_inc(v_decl_3067_);
v___x_3077_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3067_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v___x_3077_);
v___x_3079_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3066_, v_a_3078_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; 
lean_dec_ref(v___x_3079_);
v___x_3080_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3066_, v_decl_3067_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_doBlockResultType_3082_; lean_object* v___x_3083_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref(v___x_3080_);
v_doBlockResultType_3082_ = lean_ctor_get(v_a_3069_, 3);
lean_inc_ref(v_a_3069_);
lean_inc_ref(v_doBlockResultType_3082_);
v___x_3083_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_3082_, v_a_3069_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3288_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3288_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3288_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3089_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3090_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3091_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3081_);
v___x_3092_ = l_Lean_Syntax_isOfKind(v_a_3081_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
lean_dec(v_a_3081_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v___x_3093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = l_Lean_Syntax_getArg(v_a_3081_, v___x_3094_);
lean_dec(v_a_3081_);
v___x_3096_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3095_);
v___x_3097_ = l_Lean_Syntax_isOfKind(v___x_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3095_);
v___x_3099_ = l_Lean_Syntax_isOfKind(v___x_3095_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
v___x_3100_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3095_);
v___x_3101_ = l_Lean_Syntax_isOfKind(v___x_3095_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; 
lean_dec(v___x_3095_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v___x_3102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3102_;
}
else
{
lean_object* v___x_3103_; lean_object* v_id_3104_; lean_object* v_binders_3105_; lean_object* v_type_3106_; lean_object* v_value_3107_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v_id_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; uint8_t v___x_3186_; 
v___x_3103_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3095_);
lean_dec(v___x_3095_);
v_id_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_id_3104_);
v_binders_3105_ = lean_ctor_get(v___x_3103_, 1);
lean_inc_ref(v_binders_3105_);
v_type_3106_ = lean_ctor_get(v___x_3103_, 2);
lean_inc(v_type_3106_);
v_value_3107_ = lean_ctor_get(v___x_3103_, 3);
lean_inc(v_value_3107_);
lean_dec_ref(v___x_3103_);
v___x_3186_ = l_Lean_Syntax_isIdent(v_id_3104_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_id_3104_, v___x_3092_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec(v_id_3104_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v_id_3176_ = v_a_3188_;
v___y_3177_ = v_a_3069_;
v___y_3178_ = v_a_3070_;
v___y_3179_ = v_a_3071_;
v___y_3180_ = v_a_3072_;
v___y_3181_ = v_a_3073_;
v___y_3182_ = v_a_3074_;
v___y_3183_ = v_a_3075_;
goto v___jp_3175_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_value_3107_);
lean_dec(v_type_3106_);
lean_dec_ref(v_binders_3105_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v_a_3189_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3187_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3187_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
v_id_3176_ = v_id_3104_;
v___y_3177_ = v_a_3069_;
v___y_3178_ = v_a_3070_;
v___y_3179_ = v_a_3071_;
v___y_3180_ = v_a_3072_;
v___y_3181_ = v_a_3073_;
v___y_3182_ = v_a_3074_;
v___y_3183_ = v_a_3075_;
goto v___jp_3175_;
}
v___jp_3108_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; lean_object* v___x_3123_; 
v___x_3119_ = lean_box(v___x_3092_);
v___x_3120_ = lean_box(v___x_3097_);
v___x_3121_ = lean_box(v___y_3118_);
v___f_3122_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3122_, 0, v_type_3106_);
lean_closure_set(v___f_3122_, 1, v_value_3107_);
lean_closure_set(v___f_3122_, 2, v___x_3119_);
lean_closure_set(v___f_3122_, 3, v___x_3120_);
lean_closure_set(v___f_3122_, 4, v___x_3094_);
lean_closure_set(v___f_3122_, 5, v___x_3121_);
v___x_3123_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3105_, v___f_3122_, v___y_3111_, v___y_3114_, v___y_3117_, v___y_3116_, v___y_3109_, v___y_3113_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v_fst_3125_; lean_object* v_snd_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3166_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___x_3123_);
v_fst_3125_ = lean_ctor_get(v_a_3124_, 0);
v_snd_3126_ = lean_ctor_get(v_a_3124_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3128_ = v_a_3124_;
v_isShared_3129_ = v_isSharedCheck_3166_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snd_3126_);
lean_inc(v_fst_3125_);
lean_dec(v_a_3124_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3166_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3131_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3130_, v___y_3109_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; uint8_t v___x_3135_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = l_Lean_Syntax_getId(v___y_3112_);
lean_dec(v___y_3112_);
v___x_3134_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3133_);
v___x_3135_ = lean_unbox(v_a_3132_);
lean_dec(v_a_3132_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_del_object(v___x_3128_);
v___x_3136_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3133_, v_fst_3125_, v_snd_3126_, v___y_3115_, v___y_3118_, v___x_3134_, v___y_3110_, v___y_3111_, v___y_3114_, v___y_3117_, v___y_3116_, v___y_3109_, v___y_3113_);
lean_dec_ref(v___y_3110_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_inc(v___x_3133_);
v___x_3137_ = l_Lean_MessageData_ofName(v___x_3133_);
v___x_3138_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__5);
if (v_isShared_3129_ == 0)
{
lean_ctor_set_tag(v___x_3128_, 7);
lean_ctor_set(v___x_3128_, 1, v___x_3138_);
lean_ctor_set(v___x_3128_, 0, v___x_3137_);
v___x_3140_ = v___x_3128_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_inc(v_fst_3125_);
v___x_3141_ = l_Lean_MessageData_ofExpr(v_fst_3125_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__7, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__7);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
lean_inc(v_snd_3126_);
v___x_3145_ = l_Lean_MessageData_ofExpr(v_snd_3126_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3130_, v___x_3146_, v___y_3117_, v___y_3116_, v___y_3109_, v___y_3113_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v___x_3148_; 
lean_dec_ref(v___x_3147_);
v___x_3148_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3133_, v_fst_3125_, v_snd_3126_, v___y_3115_, v___y_3118_, v___x_3134_, v___y_3110_, v___y_3111_, v___y_3114_, v___y_3117_, v___y_3116_, v___y_3109_, v___y_3113_);
lean_dec_ref(v___y_3110_);
return v___x_3148_;
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v___x_3133_);
lean_dec(v_snd_3126_);
lean_dec(v_fst_3125_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___y_3110_);
v_a_3149_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3147_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3147_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_del_object(v___x_3128_);
lean_dec(v_snd_3126_);
lean_dec(v_fst_3125_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3110_);
v_a_3158_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3131_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3131_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3110_);
v_a_3167_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3123_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3123_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
v___jp_3175_:
{
lean_object* v___x_3184_; lean_object* v___f_3185_; 
v___x_3184_ = lean_box(v___x_3097_);
lean_inc(v_letOrReassign_3066_);
lean_inc(v_id_3176_);
v___f_3185_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 14, 5);
lean_closure_set(v___f_3185_, 0, v_id_3176_);
lean_closure_set(v___f_3185_, 1, v_dec_3068_);
lean_closure_set(v___f_3185_, 2, v___x_3184_);
lean_closure_set(v___f_3185_, 3, v_letOrReassign_3066_);
lean_closure_set(v___f_3185_, 4, v_a_3078_);
if (lean_obj_tag(v_letOrReassign_3066_) == 1)
{
v___y_3109_ = v___y_3182_;
v___y_3110_ = v___y_3177_;
v___y_3111_ = v___y_3178_;
v___y_3112_ = v_id_3176_;
v___y_3113_ = v___y_3183_;
v___y_3114_ = v___y_3179_;
v___y_3115_ = v___f_3185_;
v___y_3116_ = v___y_3181_;
v___y_3117_ = v___y_3180_;
v___y_3118_ = v___x_3092_;
goto v___jp_3108_;
}
else
{
lean_dec(v_letOrReassign_3066_);
v___y_3109_ = v___y_3182_;
v___y_3110_ = v___y_3177_;
v___y_3111_ = v___y_3178_;
v___y_3112_ = v_id_3176_;
v___y_3113_ = v___y_3183_;
v___y_3114_ = v___y_3179_;
v___y_3115_ = v___f_3185_;
v___y_3116_ = v___y_3181_;
v___y_3117_ = v___y_3180_;
v___y_3118_ = v___x_3097_;
goto v___jp_3108_;
}
}
}
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3197_ = lean_unsigned_to_nat(1u);
v___x_3198_ = l_Lean_Syntax_getArg(v___x_3095_, v___x_3197_);
v___x_3199_ = l_Lean_Syntax_matchesNull(v___x_3198_, v___x_3094_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec(v___x_3095_);
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v___x_3200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; lean_object* v_rhs_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v_xType_x3f_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3201_ = l_Lean_Syntax_getArg(v___x_3095_, v___x_3094_);
v___x_3256_ = lean_unsigned_to_nat(2u);
v___x_3257_ = l_Lean_Syntax_getArg(v___x_3095_, v___x_3256_);
v___x_3258_ = l_Lean_Syntax_isNone(v___x_3257_);
if (v___x_3258_ == 0)
{
uint8_t v___x_3259_; 
lean_inc(v___x_3257_);
v___x_3259_ = l_Lean_Syntax_matchesNull(v___x_3257_, v___x_3197_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec(v___x_3257_);
lean_dec(v___x_3201_);
lean_dec(v___x_3095_);
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v___x_3260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3261_ = l_Lean_Syntax_getArg(v___x_3257_, v___x_3094_);
lean_dec(v___x_3257_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3261_);
v___x_3263_ = l_Lean_Syntax_isOfKind(v___x_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_dec(v___x_3261_);
lean_dec(v___x_3201_);
lean_dec(v___x_3095_);
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v___x_3264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = l_Lean_Syntax_getArg(v___x_3261_, v___x_3197_);
lean_dec(v___x_3261_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set_tag(v___x_3086_, 1);
lean_ctor_set(v___x_3086_, 0, v___x_3265_);
v___x_3267_ = v___x_3086_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_inc_ref(v_a_3074_);
v_xType_x3f_3222_ = v___x_3267_;
v___y_3223_ = v_a_3069_;
v___y_3224_ = v_a_3070_;
v___y_3225_ = v_a_3071_;
v___y_3226_ = v_a_3072_;
v___y_3227_ = v_a_3073_;
v___y_3228_ = v_a_3074_;
v___y_3229_ = v_a_3075_;
goto v___jp_3221_;
}
}
}
}
else
{
lean_object* v___x_3269_; 
lean_dec(v___x_3257_);
lean_del_object(v___x_3086_);
v___x_3269_ = lean_box(0);
lean_inc_ref(v_a_3074_);
v_xType_x3f_3222_ = v___x_3269_;
v___y_3223_ = v_a_3069_;
v___y_3224_ = v_a_3070_;
v___y_3225_ = v_a_3071_;
v___y_3226_ = v_a_3072_;
v___y_3227_ = v_a_3073_;
v___y_3228_ = v_a_3074_;
v___y_3229_ = v_a_3075_;
goto v___jp_3221_;
}
v___jp_3202_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3211_ = lean_box(v___x_3097_);
v___x_3212_ = lean_box(v___x_3092_);
lean_inc(v___x_3201_);
v___f_3213_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 17, 8);
lean_closure_set(v___f_3213_, 0, v_a_3084_);
lean_closure_set(v___f_3213_, 1, v_rhs_3203_);
lean_closure_set(v___f_3213_, 2, v___x_3211_);
lean_closure_set(v___f_3213_, 3, v___x_3088_);
lean_closure_set(v___f_3213_, 4, v___x_3089_);
lean_closure_set(v___f_3213_, 5, v___x_3090_);
lean_closure_set(v___f_3213_, 6, v___x_3201_);
lean_closure_set(v___f_3213_, 7, v___x_3212_);
v___x_3214_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3214_, 0, v_dec_3068_);
v___x_3215_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3215_, 0, v_letOrReassign_3066_);
lean_closure_set(v___x_3215_, 1, v_a_3078_);
lean_closure_set(v___x_3215_, 2, v___x_3214_);
v___x_3216_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__9, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__9);
v___x_3217_ = l_Lean_MessageData_ofSyntax(v___x_3201_);
v___x_3218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_box(0);
v___x_3220_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3218_, v___x_3215_, v___f_3213_, v___x_3219_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3204_);
return v___x_3220_;
}
v___jp_3221_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_unsigned_to_nat(4u);
v___x_3231_ = l_Lean_Syntax_getArg(v___x_3095_, v___x_3230_);
lean_dec(v___x_3095_);
if (lean_obj_tag(v_xType_x3f_3222_) == 0)
{
v_rhs_3203_ = v___x_3231_;
v___y_3204_ = v___y_3223_;
v___y_3205_ = v___y_3224_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___y_3229_;
goto v___jp_3202_;
}
else
{
lean_object* v_val_3232_; lean_object* v_ref_3233_; lean_object* v_quotContext_3234_; lean_object* v_currMacroScope_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_val_3232_ = lean_ctor_get(v_xType_x3f_3222_, 0);
lean_inc(v_val_3232_);
lean_dec_ref(v_xType_x3f_3222_);
v_ref_3233_ = lean_ctor_get(v___y_3228_, 5);
v_quotContext_3234_ = lean_ctor_get(v___y_3228_, 10);
v_currMacroScope_3235_ = lean_ctor_get(v___y_3228_, 11);
v___x_3236_ = l_Lean_SourceInfo_fromRef(v_ref_3233_, v___x_3097_);
v___x_3237_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3238_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3239_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3236_);
v___x_3240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3236_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3242_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3243_ = lean_box(0);
lean_inc(v_currMacroScope_3235_);
lean_inc(v_quotContext_3234_);
v___x_3244_ = l_Lean_addMacroScope(v_quotContext_3234_, v___x_3243_, v_currMacroScope_3235_);
v___x_3245_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
lean_inc(v___x_3236_);
v___x_3246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3236_);
lean_ctor_set(v___x_3246_, 1, v___x_3242_);
lean_ctor_set(v___x_3246_, 2, v___x_3244_);
lean_ctor_set(v___x_3246_, 3, v___x_3245_);
lean_inc(v___x_3236_);
v___x_3247_ = l_Lean_Syntax_node1(v___x_3236_, v___x_3241_, v___x_3246_);
lean_inc(v___x_3236_);
v___x_3248_ = l_Lean_Syntax_node2(v___x_3236_, v___x_3238_, v___x_3240_, v___x_3247_);
v___x_3249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_3236_);
v___x_3250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3236_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
lean_inc(v___x_3236_);
v___x_3252_ = l_Lean_Syntax_node1(v___x_3236_, v___x_3251_, v_val_3232_);
v___x_3253_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
lean_inc(v___x_3236_);
v___x_3254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3236_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_Syntax_node5(v___x_3236_, v___x_3237_, v___x_3248_, v___x_3231_, v___x_3250_, v___x_3252_, v___x_3254_);
v_rhs_3203_ = v___x_3255_;
v___y_3204_ = v___y_3223_;
v___y_3205_ = v___y_3224_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___y_3229_;
goto v___jp_3202_;
}
}
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_del_object(v___x_3086_);
lean_dec(v_a_3084_);
lean_dec(v_a_3078_);
v___x_3270_ = lean_box(v___x_3092_);
lean_inc(v___x_3095_);
v___x_3271_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3271_, 0, v___x_3095_);
lean_closure_set(v___x_3271_, 1, v___x_3270_);
lean_inc_ref(v_a_3074_);
v___x_3272_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v___x_3271_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v_ref_3274_; uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref(v___x_3272_);
v_ref_3274_ = lean_ctor_get(v_a_3074_, 5);
v___x_3275_ = 0;
v___x_3276_ = l_Lean_SourceInfo_fromRef(v_ref_3274_, v___x_3275_);
v___x_3277_ = l_Lean_Syntax_node1(v___x_3276_, v___x_3091_, v_a_3273_);
lean_inc(v___x_3277_);
v___x_3278_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 11, 3);
lean_closure_set(v___x_3278_, 0, v_letOrReassign_3066_);
lean_closure_set(v___x_3278_, 1, v___x_3277_);
lean_closure_set(v___x_3278_, 2, v_dec_3068_);
v___x_3279_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3095_, v___x_3277_, v___x_3278_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec_ref(v_a_3069_);
return v___x_3279_;
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v___x_3095_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v_a_3280_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3272_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3272_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3081_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
return v___x_3083_;
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_letOrReassign_3066_);
v_a_3289_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3080_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3080_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_decl_3067_);
lean_dec(v_letOrReassign_3066_);
v_a_3297_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3079_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3079_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref(v_a_3069_);
lean_dec_ref(v_dec_3068_);
lean_dec(v_decl_3067_);
lean_dec(v_letOrReassign_3066_);
v_a_3305_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3077_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3077_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3314_, v_x_3315_, v_x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_cls_3318_, lean_object* v_msg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_cls_3318_, v_msg_3319_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_cls_3329_, lean_object* v_msg_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_cls_3329_, v_msg_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9(lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___redArg(v___y_3345_, v___y_3346_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9___boxed(lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__9(v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3358_, lean_object* v_beforeStx_3359_, lean_object* v_afterStx_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_beforeStx_3359_, v_afterStx_3360_, v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3371_, lean_object* v_beforeStx_3372_, lean_object* v_afterStx_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3371_, v_beforeStx_3372_, v_afterStx_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec_ref(v___y_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13(lean_object* v_00_u03b1_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___redArg(v_x_3385_, v___y_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3389_, lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__13(v_00_u03b1_3389_, v_x_3390_, v___y_3391_, v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec_ref(v_x_3390_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18(lean_object* v_00_u03b1_3394_, lean_object* v_ref_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___redArg(v_ref_3395_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18___boxed(lean_object* v_00_u03b1_3405_, lean_object* v_ref_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__18(v_00_u03b1_3405_, v_ref_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10(lean_object* v_00_u03b1_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v___x_3426_; 
lean_inc_ref(v___y_3423_);
v___x_3426_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___redArg(v_x_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10___boxed(lean_object* v_00_u03b1_3427_, lean_object* v_x_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10(v_00_u03b1_3427_, v_x_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec_ref(v___y_3429_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3438_, lean_object* v_x_3439_, size_t v_x_3440_, size_t v_x_3441_, lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3439_, v_x_3440_, v_x_3441_, v_x_3442_, v_x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3445_, lean_object* v_x_3446_, lean_object* v_x_3447_, lean_object* v_x_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
size_t v_x_77709__boxed_3451_; size_t v_x_77710__boxed_3452_; lean_object* v_res_3453_; 
v_x_77709__boxed_3451_ = lean_unbox_usize(v_x_3447_);
lean_dec(v_x_3447_);
v_x_77710__boxed_3452_ = lean_unbox_usize(v_x_3448_);
lean_dec(v_x_3448_);
v_res_3453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3445_, v_x_3446_, v_x_77709__boxed_3451_, v_x_77710__boxed_3452_, v_x_3449_, v_x_3450_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11(lean_object* v_00_u03b1_3454_, lean_object* v_stx_3455_, lean_object* v_output_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___redArg(v_stx_3455_, v_output_3456_, v_x_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11___boxed(lean_object* v_00_u03b1_3466_, lean_object* v_stx_3467_, lean_object* v_output_3468_, lean_object* v_x_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11(v_00_u03b1_3466_, v_stx_3467_, v_output_3468_, v_x_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15(lean_object* v_as_3478_, lean_object* v_as_x27_3479_, lean_object* v_b_3480_, lean_object* v_a_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___redArg(v_as_x27_3479_, v_b_3480_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15___boxed(lean_object* v_as_3491_, lean_object* v_as_x27_3492_, lean_object* v_b_3493_, lean_object* v_a_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__15(v_as_3491_, v_as_x27_3492_, v_b_3493_, v_a_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v_as_3491_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17(lean_object* v_00_u03b1_3504_, lean_object* v_ref_3505_, lean_object* v_msg_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___redArg(v_ref_3505_, v_msg_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17___boxed(lean_object* v_00_u03b1_3516_, lean_object* v_ref_3517_, lean_object* v_msg_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17(v_00_u03b1_3516_, v_ref_3517_, v_msg_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v_ref_3517_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3528_, lean_object* v_n_3529_, lean_object* v_k_3530_, lean_object* v_v_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_n_3529_, v_k_3530_, v_v_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_3533_, size_t v_depth_3534_, lean_object* v_keys_3535_, lean_object* v_vals_3536_, lean_object* v_heq_3537_, lean_object* v_i_3538_, lean_object* v_entries_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___redArg(v_depth_3534_, v_keys_3535_, v_vals_3536_, v_i_3538_, v_entries_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_3541_, lean_object* v_depth_3542_, lean_object* v_keys_3543_, lean_object* v_vals_3544_, lean_object* v_heq_3545_, lean_object* v_i_3546_, lean_object* v_entries_3547_){
_start:
{
size_t v_depth_boxed_3548_; lean_object* v_res_3549_; 
v_depth_boxed_3548_ = lean_unbox_usize(v_depth_3542_);
lean_dec(v_depth_3542_);
v_res_3549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__6(v_00_u03b2_3541_, v_depth_boxed_3548_, v_keys_3543_, v_vals_3544_, v_heq_3545_, v_i_3546_, v_entries_3547_);
lean_dec_ref(v_vals_3544_);
lean_dec_ref(v_keys_3543_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19(lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___redArg(v___y_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19___boxed(lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14_spec__19(v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14(lean_object* v_00_u03b1_3566_, lean_object* v_x_3567_, lean_object* v_mkInfoTree_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___redArg(v_x_3567_, v_mkInfoTree_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_x_3578_, lean_object* v_mkInfoTree_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__11_spec__14(v_00_u03b1_3577_, v_x_3578_, v_mkInfoTree_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23(lean_object* v_00_u03b1_3588_, lean_object* v_msg_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v_msg_3589_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___boxed(lean_object* v_00_u03b1_3599_, lean_object* v_msg_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23(v_00_u03b1_3599_, v_msg_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15(lean_object* v_00_u03b2_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5_spec__15___redArg(v_x_3611_, v_x_3612_, v_x_3613_, v_x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22(lean_object* v_00_u03b2_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
uint8_t v___x_3619_; 
v___x_3619_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___redArg(v_x_3617_, v_x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22___boxed(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
uint8_t v_res_3623_; lean_object* v_r_3624_; 
v_res_3623_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22(v_00_u03b2_3620_, v_x_3621_, v_x_3622_);
lean_dec_ref(v_x_3622_);
v_r_3624_ = lean_box(v_res_3623_);
return v_r_3624_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26(lean_object* v_00_u03b2_3625_, lean_object* v_x_3626_, size_t v_x_3627_, lean_object* v_x_3628_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___redArg(v_x_3626_, v_x_3627_, v_x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26___boxed(lean_object* v_00_u03b2_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
size_t v_x_77898__boxed_3634_; uint8_t v_res_3635_; lean_object* v_r_3636_; 
v_x_77898__boxed_3634_ = lean_unbox_usize(v_x_3632_);
lean_dec(v_x_3632_);
v_res_3635_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26(v_00_u03b2_3630_, v_x_3631_, v_x_77898__boxed_3634_, v_x_3633_);
lean_dec_ref(v_x_3633_);
v_r_3636_ = lean_box(v_res_3635_);
return v_r_3636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29(lean_object* v_00_u03b2_3637_, lean_object* v_keys_3638_, lean_object* v_vals_3639_, lean_object* v_heq_3640_, lean_object* v_i_3641_, lean_object* v_k_3642_){
_start:
{
uint8_t v___x_3643_; 
v___x_3643_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___redArg(v_keys_3638_, v_i_3641_, v_k_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29___boxed(lean_object* v_00_u03b2_3644_, lean_object* v_keys_3645_, lean_object* v_vals_3646_, lean_object* v_heq_3647_, lean_object* v_i_3648_, lean_object* v_k_3649_){
_start:
{
uint8_t v_res_3650_; lean_object* v_r_3651_; 
v_res_3650_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__14_spec__18_spec__22_spec__26_spec__29(v_00_u03b2_3644_, v_keys_3645_, v_vals_3646_, v_heq_3647_, v_i_3648_, v_k_3649_);
lean_dec_ref(v_k_3649_);
lean_dec_ref(v_vals_3646_);
lean_dec_ref(v_keys_3645_);
v_r_3651_ = lean_box(v_res_3650_);
return v_r_3651_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3660_, lean_object* v_otherwise_x3f_3661_, uint8_t v___x_3662_, lean_object* v___x_3663_, lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v___x_3666_, lean_object* v___x_3667_, lean_object* v_dec_3668_, uint8_t v___x_3669_, lean_object* v___y_3670_, lean_object* v___x_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; uint8_t v___y_3703_; 
switch(lean_obj_tag(v_letOrReassign_3660_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3661_) == 1)
{
lean_object* v_mutTk_x3f_3714_; lean_object* v_val_3715_; lean_object* v_ref_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3734_; 
v_mutTk_x3f_3714_ = lean_ctor_get(v_letOrReassign_3660_, 0);
v_val_3715_ = lean_ctor_get(v_otherwise_x3f_3661_, 0);
lean_inc(v_val_3715_);
lean_dec_ref(v_otherwise_x3f_3661_);
v_ref_3716_ = lean_ctor_get(v___y_3677_, 5);
v___x_3717_ = l_Lean_SourceInfo_fromRef(v_ref_3716_, v___x_3662_);
v___x_3718_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
v___x_3719_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3718_);
v___x_3720_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3717_);
v___x_3721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3717_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3723_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3714_) == 1)
{
lean_object* v_val_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_val_3745_ = lean_ctor_get(v_mutTk_x3f_3714_, 0);
v___x_3746_ = l_Lean_SourceInfo_fromRef(v_val_3745_, v___x_3669_);
v___x_3747_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = l_Array_mkArray1___redArg(v___x_3748_);
v___y_3734_ = v___x_3749_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___y_3734_ = v___x_3750_;
goto v___jp_3733_;
}
v___jp_3724_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3729_ = l_Array_append___redArg(v___x_3723_, v___y_3728_);
lean_dec_ref(v___y_3728_);
lean_inc(v___x_3717_);
v___x_3730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3717_);
lean_ctor_set(v___x_3730_, 1, v___x_3722_);
lean_ctor_set(v___x_3730_, 2, v___x_3729_);
v___x_3731_ = l_Lean_Syntax_node8(v___x_3717_, v___x_3719_, v___x_3721_, v___y_3726_, v___x_3666_, v___y_3727_, v___x_3667_, v___y_3725_, v_val_3715_, v___x_3730_);
v___x_3732_ = l_Lean_Elab_Do_elabDoElem(v___x_3731_, v_dec_3668_, v___x_3669_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3732_;
}
v___jp_3733_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3735_ = l_Array_append___redArg(v___x_3723_, v___y_3734_);
lean_dec_ref(v___y_3734_);
lean_inc(v___x_3717_);
v___x_3736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3717_);
lean_ctor_set(v___x_3736_, 1, v___x_3722_);
lean_ctor_set(v___x_3736_, 2, v___x_3735_);
v___x_3737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3717_);
v___x_3738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3717_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_3717_);
v___x_3740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3717_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
if (lean_obj_tag(v___y_3670_) == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___y_3725_ = v___x_3740_;
v___y_3726_ = v___x_3736_;
v___y_3727_ = v___x_3738_;
v___y_3728_ = v___x_3741_;
goto v___jp_3724_;
}
else
{
lean_object* v_val_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_val_3742_ = lean_ctor_get(v___y_3670_, 0);
lean_inc(v_val_3742_);
lean_dec_ref(v___y_3670_);
v___x_3743_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___x_3744_ = lean_array_push(v___x_3743_, v_val_3742_);
v___y_3725_ = v___x_3740_;
v___y_3726_ = v___x_3736_;
v___y_3727_ = v___x_3738_;
v___y_3728_ = v___x_3744_;
goto v___jp_3724_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3751_; lean_object* v_ref_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___y_3761_; 
lean_dec(v___y_3670_);
lean_dec(v_otherwise_x3f_3661_);
v_mutTk_x3f_3751_ = lean_ctor_get(v_letOrReassign_3660_, 0);
v_ref_3752_ = lean_ctor_get(v___y_3677_, 5);
v___x_3753_ = l_Lean_SourceInfo_fromRef(v_ref_3752_, v___x_3662_);
v___x_3754_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v___x_3663_);
v___x_3755_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3754_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3753_);
v___x_3757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3753_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3759_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3751_) == 1)
{
lean_object* v_val_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_val_3775_ = lean_ctor_get(v_mutTk_x3f_3751_, 0);
v___x_3776_ = l_Lean_SourceInfo_fromRef(v_val_3775_, v___x_3669_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = l_Array_mkArray1___redArg(v___x_3778_);
v___y_3761_ = v___x_3779_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_mk_empty_array_with_capacity(v___x_3671_);
v___y_3761_ = v___x_3780_;
goto v___jp_3760_;
}
v___jp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3762_ = l_Array_append___redArg(v___x_3759_, v___y_3761_);
lean_dec_ref(v___y_3761_);
lean_inc(v___x_3753_);
v___x_3763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3753_);
lean_ctor_set(v___x_3763_, 1, v___x_3758_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v___x_3663_);
v___x_3765_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3764_);
v___x_3766_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3767_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3766_);
lean_inc(v___x_3753_);
v___x_3768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3753_);
lean_ctor_set(v___x_3768_, 1, v___x_3758_);
lean_ctor_set(v___x_3768_, 2, v___x_3759_);
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3753_);
v___x_3770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3753_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
lean_inc_ref(v___x_3768_);
lean_inc(v___x_3753_);
v___x_3771_ = l_Lean_Syntax_node5(v___x_3753_, v___x_3767_, v___x_3666_, v___x_3768_, v___x_3768_, v___x_3770_, v___x_3667_);
lean_inc(v___x_3753_);
v___x_3772_ = l_Lean_Syntax_node1(v___x_3753_, v___x_3765_, v___x_3771_);
v___x_3773_ = l_Lean_Syntax_node3(v___x_3753_, v___x_3755_, v___x_3757_, v___x_3763_, v___x_3772_);
v___x_3774_ = l_Lean_Elab_Do_elabDoElem(v___x_3773_, v_dec_3668_, v___x_3669_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3774_;
}
}
}
case 1:
{
lean_dec(v___y_3670_);
if (lean_obj_tag(v_otherwise_x3f_3661_) == 1)
{
lean_object* v___x_3781_; 
lean_dec_ref(v_otherwise_x3f_3661_);
lean_dec_ref(v_dec_3668_);
lean_dec(v___x_3667_);
lean_dec(v___x_3666_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___x_3663_);
v___x_3781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3781_;
}
else
{
lean_object* v_ref_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_dec(v_otherwise_x3f_3661_);
v_ref_3782_ = lean_ctor_get(v___y_3677_, 5);
v___x_3783_ = l_Lean_SourceInfo_fromRef(v_ref_3782_, v___x_3662_);
v___x_3784_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v___x_3663_);
v___x_3785_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3784_);
v___x_3786_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc(v___x_3783_);
v___x_3787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3783_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v___x_3663_);
v___x_3789_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3788_);
v___x_3790_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3791_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3790_);
v___x_3792_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3793_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3783_);
v___x_3794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3783_);
lean_ctor_set(v___x_3794_, 1, v___x_3792_);
lean_ctor_set(v___x_3794_, 2, v___x_3793_);
v___x_3795_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3783_);
v___x_3796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3783_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
lean_inc_ref(v___x_3794_);
lean_inc(v___x_3783_);
v___x_3797_ = l_Lean_Syntax_node5(v___x_3783_, v___x_3791_, v___x_3666_, v___x_3794_, v___x_3794_, v___x_3796_, v___x_3667_);
lean_inc(v___x_3783_);
v___x_3798_ = l_Lean_Syntax_node1(v___x_3783_, v___x_3789_, v___x_3797_);
v___x_3799_ = l_Lean_Syntax_node2(v___x_3783_, v___x_3785_, v___x_3787_, v___x_3798_);
v___x_3800_ = l_Lean_Elab_Do_elabDoElem(v___x_3799_, v_dec_3668_, v___x_3669_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3800_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3661_);
if (lean_obj_tag(v___y_3670_) == 0)
{
v___y_3703_ = v___x_3669_;
goto v___jp_3702_;
}
else
{
lean_dec_ref(v___y_3670_);
v___y_3703_ = v___x_3662_;
goto v___jp_3702_;
}
}
}
v___jp_3680_:
{
lean_object* v_ref_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_ref_3688_ = lean_ctor_get(v___y_3686_, 5);
v___x_3689_ = l_Lean_SourceInfo_fromRef(v_ref_3688_, v___x_3662_);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
lean_inc_ref(v___x_3663_);
v___x_3691_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3690_);
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3693_ = l_Lean_Name_mkStr4(v___x_3663_, v___x_3664_, v___x_3665_, v___x_3692_);
v___x_3694_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3695_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3689_);
v___x_3696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3689_);
lean_ctor_set(v___x_3696_, 1, v___x_3694_);
lean_ctor_set(v___x_3696_, 2, v___x_3695_);
v___x_3697_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3689_);
v___x_3698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3689_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
lean_inc_ref(v___x_3696_);
lean_inc(v___x_3689_);
v___x_3699_ = l_Lean_Syntax_node5(v___x_3689_, v___x_3693_, v___x_3666_, v___x_3696_, v___x_3696_, v___x_3698_, v___x_3667_);
v___x_3700_ = l_Lean_Syntax_node1(v___x_3689_, v___x_3691_, v___x_3699_);
v___x_3701_ = l_Lean_Elab_Do_elabDoElem(v___x_3700_, v_dec_3668_, v___x_3669_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3701_;
}
v___jp_3702_:
{
if (v___y_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_dec_3668_);
lean_dec(v___x_3667_);
lean_dec(v___x_3666_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3664_);
lean_dec_ref(v___x_3663_);
v___x_3704_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3705_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v___x_3704_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
v___y_3681_ = v___y_3672_;
v___y_3682_ = v___y_3673_;
v___y_3683_ = v___y_3674_;
v___y_3684_ = v___y_3675_;
v___y_3685_ = v___y_3676_;
v___y_3686_ = v___y_3677_;
v___y_3687_ = v___y_3678_;
goto v___jp_3680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_3801_ = _args[0];
lean_object* v_otherwise_x3f_3802_ = _args[1];
lean_object* v___x_3803_ = _args[2];
lean_object* v___x_3804_ = _args[3];
lean_object* v___x_3805_ = _args[4];
lean_object* v___x_3806_ = _args[5];
lean_object* v___x_3807_ = _args[6];
lean_object* v___x_3808_ = _args[7];
lean_object* v_dec_3809_ = _args[8];
lean_object* v___x_3810_ = _args[9];
lean_object* v___y_3811_ = _args[10];
lean_object* v___x_3812_ = _args[11];
lean_object* v___y_3813_ = _args[12];
lean_object* v___y_3814_ = _args[13];
lean_object* v___y_3815_ = _args[14];
lean_object* v___y_3816_ = _args[15];
lean_object* v___y_3817_ = _args[16];
lean_object* v___y_3818_ = _args[17];
lean_object* v___y_3819_ = _args[18];
lean_object* v___y_3820_ = _args[19];
_start:
{
uint8_t v___x_37142__boxed_3821_; uint8_t v___x_37148__boxed_3822_; lean_object* v_res_3823_; 
v___x_37142__boxed_3821_ = lean_unbox(v___x_3803_);
v___x_37148__boxed_3822_ = lean_unbox(v___x_3810_);
v_res_3823_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_3801_, v_otherwise_x3f_3802_, v___x_37142__boxed_3821_, v___x_3804_, v___x_3805_, v___x_3806_, v___x_3807_, v___x_3808_, v_dec_3809_, v___x_37148__boxed_3822_, v___y_3811_, v___x_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___x_3812_);
lean_dec(v_letOrReassign_3801_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_3824_, lean_object* v_otherwise_x3f_3825_, uint8_t v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v___x_3829_, lean_object* v___x_3830_, lean_object* v___x_3831_, lean_object* v_dec_3832_, uint8_t v___x_3833_, lean_object* v___y_3834_, lean_object* v___x_3835_, uint8_t v___x_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; uint8_t v___y_3868_; 
switch(lean_obj_tag(v_letOrReassign_3824_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3825_) == 1)
{
lean_object* v_mutTk_x3f_3879_; lean_object* v_val_3880_; lean_object* v_ref_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3899_; 
v_mutTk_x3f_3879_ = lean_ctor_get(v_letOrReassign_3824_, 0);
v_val_3880_ = lean_ctor_get(v_otherwise_x3f_3825_, 0);
lean_inc(v_val_3880_);
lean_dec_ref(v_otherwise_x3f_3825_);
v_ref_3881_ = lean_ctor_get(v___y_3842_, 5);
v___x_3882_ = l_Lean_SourceInfo_fromRef(v_ref_3881_, v___x_3826_);
v___x_3883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
v___x_3884_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3883_);
v___x_3885_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3882_);
v___x_3886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3882_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3888_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3879_) == 1)
{
lean_object* v_val_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_val_3910_ = lean_ctor_get(v_mutTk_x3f_3879_, 0);
v___x_3911_ = l_Lean_SourceInfo_fromRef(v_val_3910_, v___x_3833_);
v___x_3912_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = l_Array_mkArray1___redArg(v___x_3913_);
v___y_3899_ = v___x_3914_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3915_; 
v___x_3915_ = lean_mk_empty_array_with_capacity(v___x_3835_);
v___y_3899_ = v___x_3915_;
goto v___jp_3898_;
}
v___jp_3889_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = l_Array_append___redArg(v___x_3888_, v___y_3893_);
lean_dec_ref(v___y_3893_);
lean_inc(v___x_3882_);
v___x_3895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3882_);
lean_ctor_set(v___x_3895_, 1, v___x_3887_);
lean_ctor_set(v___x_3895_, 2, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_node8(v___x_3882_, v___x_3884_, v___x_3886_, v___y_3892_, v___x_3830_, v___y_3890_, v___x_3831_, v___y_3891_, v_val_3880_, v___x_3895_);
v___x_3897_ = l_Lean_Elab_Do_elabDoElem(v___x_3896_, v_dec_3832_, v___x_3833_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3897_;
}
v___jp_3898_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3900_ = l_Array_append___redArg(v___x_3888_, v___y_3899_);
lean_dec_ref(v___y_3899_);
lean_inc(v___x_3882_);
v___x_3901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3882_);
lean_ctor_set(v___x_3901_, 1, v___x_3887_);
lean_ctor_set(v___x_3901_, 2, v___x_3900_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3882_);
v___x_3903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3882_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_3882_);
v___x_3905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3882_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
if (lean_obj_tag(v___y_3834_) == 0)
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_mk_empty_array_with_capacity(v___x_3835_);
v___y_3890_ = v___x_3903_;
v___y_3891_ = v___x_3905_;
v___y_3892_ = v___x_3901_;
v___y_3893_ = v___x_3906_;
goto v___jp_3889_;
}
else
{
lean_object* v_val_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_val_3907_ = lean_ctor_get(v___y_3834_, 0);
lean_inc(v_val_3907_);
lean_dec_ref(v___y_3834_);
v___x_3908_ = lean_mk_empty_array_with_capacity(v___x_3835_);
v___x_3909_ = lean_array_push(v___x_3908_, v_val_3907_);
v___y_3890_ = v___x_3903_;
v___y_3891_ = v___x_3905_;
v___y_3892_ = v___x_3901_;
v___y_3893_ = v___x_3909_;
goto v___jp_3889_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3916_; lean_object* v_ref_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___y_3926_; 
lean_dec(v___y_3834_);
lean_dec(v_otherwise_x3f_3825_);
v_mutTk_x3f_3916_ = lean_ctor_get(v_letOrReassign_3824_, 0);
v_ref_3917_ = lean_ctor_get(v___y_3842_, 5);
v___x_3918_ = l_Lean_SourceInfo_fromRef(v_ref_3917_, v___x_3826_);
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
lean_inc_ref(v___x_3829_);
lean_inc_ref(v___x_3828_);
lean_inc_ref(v___x_3827_);
v___x_3920_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3918_);
v___x_3922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3918_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3924_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3916_) == 1)
{
lean_object* v_val_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_val_3940_ = lean_ctor_get(v_mutTk_x3f_3916_, 0);
v___x_3941_ = l_Lean_SourceInfo_fromRef(v_val_3940_, v___x_3833_);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Array_mkArray1___redArg(v___x_3943_);
v___y_3926_ = v___x_3944_;
goto v___jp_3925_;
}
else
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_mk_empty_array_with_capacity(v___x_3835_);
v___y_3926_ = v___x_3945_;
goto v___jp_3925_;
}
v___jp_3925_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3927_ = l_Array_append___redArg(v___x_3924_, v___y_3926_);
lean_dec_ref(v___y_3926_);
lean_inc(v___x_3918_);
v___x_3928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3918_);
lean_ctor_set(v___x_3928_, 1, v___x_3923_);
lean_ctor_set(v___x_3928_, 2, v___x_3927_);
v___x_3929_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3829_);
lean_inc_ref(v___x_3828_);
lean_inc_ref(v___x_3827_);
v___x_3930_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3929_);
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3932_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3931_);
lean_inc(v___x_3918_);
v___x_3933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3918_);
lean_ctor_set(v___x_3933_, 1, v___x_3923_);
lean_ctor_set(v___x_3933_, 2, v___x_3924_);
v___x_3934_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3918_);
v___x_3935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3918_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
lean_inc_ref(v___x_3933_);
lean_inc(v___x_3918_);
v___x_3936_ = l_Lean_Syntax_node5(v___x_3918_, v___x_3932_, v___x_3830_, v___x_3933_, v___x_3933_, v___x_3935_, v___x_3831_);
lean_inc(v___x_3918_);
v___x_3937_ = l_Lean_Syntax_node1(v___x_3918_, v___x_3930_, v___x_3936_);
v___x_3938_ = l_Lean_Syntax_node3(v___x_3918_, v___x_3920_, v___x_3922_, v___x_3928_, v___x_3937_);
v___x_3939_ = l_Lean_Elab_Do_elabDoElem(v___x_3938_, v_dec_3832_, v___x_3833_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3939_;
}
}
}
case 1:
{
lean_dec(v___y_3834_);
if (lean_obj_tag(v_otherwise_x3f_3825_) == 1)
{
lean_object* v___x_3946_; 
lean_dec_ref(v_otherwise_x3f_3825_);
lean_dec_ref(v_dec_3832_);
lean_dec(v___x_3831_);
lean_dec(v___x_3830_);
lean_dec_ref(v___x_3829_);
lean_dec_ref(v___x_3828_);
lean_dec_ref(v___x_3827_);
v___x_3946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3946_;
}
else
{
lean_object* v_ref_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec(v_otherwise_x3f_3825_);
v_ref_3947_ = lean_ctor_get(v___y_3842_, 5);
v___x_3948_ = l_Lean_SourceInfo_fromRef(v_ref_3947_, v___x_3826_);
v___x_3949_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3829_);
lean_inc_ref(v___x_3828_);
lean_inc_ref(v___x_3827_);
v___x_3950_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3949_);
v___x_3951_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc(v___x_3948_);
v___x_3952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3948_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_3829_);
lean_inc_ref(v___x_3828_);
lean_inc_ref(v___x_3827_);
v___x_3954_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3953_);
v___x_3955_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3956_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3955_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3958_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3948_);
v___x_3959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3948_);
lean_ctor_set(v___x_3959_, 1, v___x_3957_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3948_);
v___x_3961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3948_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
lean_inc_ref(v___x_3959_);
lean_inc(v___x_3948_);
v___x_3962_ = l_Lean_Syntax_node5(v___x_3948_, v___x_3956_, v___x_3830_, v___x_3959_, v___x_3959_, v___x_3961_, v___x_3831_);
lean_inc(v___x_3948_);
v___x_3963_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3954_, v___x_3962_);
v___x_3964_ = l_Lean_Syntax_node2(v___x_3948_, v___x_3950_, v___x_3952_, v___x_3963_);
v___x_3965_ = l_Lean_Elab_Do_elabDoElem(v___x_3964_, v_dec_3832_, v___x_3833_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3965_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3825_);
if (lean_obj_tag(v___y_3834_) == 0)
{
v___y_3868_ = v___x_3836_;
goto v___jp_3867_;
}
else
{
lean_dec_ref(v___y_3834_);
v___y_3868_ = v___x_3826_;
goto v___jp_3867_;
}
}
}
v___jp_3845_:
{
lean_object* v_ref_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_ref_3853_ = lean_ctor_get(v___y_3851_, 5);
v___x_3854_ = l_Lean_SourceInfo_fromRef(v_ref_3853_, v___x_3826_);
v___x_3855_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3829_);
lean_inc_ref(v___x_3828_);
lean_inc_ref(v___x_3827_);
v___x_3856_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3855_);
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3858_ = l_Lean_Name_mkStr4(v___x_3827_, v___x_3828_, v___x_3829_, v___x_3857_);
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3860_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_3854_);
v___x_3861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3854_);
lean_ctor_set(v___x_3861_, 1, v___x_3859_);
lean_ctor_set(v___x_3861_, 2, v___x_3860_);
v___x_3862_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_3854_);
v___x_3863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3854_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
lean_inc_ref(v___x_3861_);
lean_inc(v___x_3854_);
v___x_3864_ = l_Lean_Syntax_node5(v___x_3854_, v___x_3858_, v___x_3830_, v___x_3861_, v___x_3861_, v___x_3863_, v___x_3831_);
v___x_3865_ = l_Lean_Syntax_node1(v___x_3854_, v___x_3856_, v___x_3864_);
v___x_3866_ = l_Lean_Elab_Do_elabDoElem(v___x_3865_, v_dec_3832_, v___x_3833_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3866_;
}
v___jp_3867_:
{
if (v___y_3868_ == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_dec_3832_);
lean_dec(v___x_3831_);
lean_dec(v___x_3830_);
lean_dec_ref(v___x_3829_);
lean_dec_ref(v___x_3828_);
lean_dec_ref(v___x_3827_);
v___x_3869_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3870_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__10_spec__17_spec__23___redArg(v___x_3869_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
else
{
v___y_3846_ = v___y_3837_;
v___y_3847_ = v___y_3838_;
v___y_3848_ = v___y_3839_;
v___y_3849_ = v___y_3840_;
v___y_3850_ = v___y_3841_;
v___y_3851_ = v___y_3842_;
v___y_3852_ = v___y_3843_;
goto v___jp_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_3966_ = _args[0];
lean_object* v_otherwise_x3f_3967_ = _args[1];
lean_object* v___x_3968_ = _args[2];
lean_object* v___x_3969_ = _args[3];
lean_object* v___x_3970_ = _args[4];
lean_object* v___x_3971_ = _args[5];
lean_object* v___x_3972_ = _args[6];
lean_object* v___x_3973_ = _args[7];
lean_object* v_dec_3974_ = _args[8];
lean_object* v___x_3975_ = _args[9];
lean_object* v___y_3976_ = _args[10];
lean_object* v___x_3977_ = _args[11];
lean_object* v___x_3978_ = _args[12];
lean_object* v___y_3979_ = _args[13];
lean_object* v___y_3980_ = _args[14];
lean_object* v___y_3981_ = _args[15];
lean_object* v___y_3982_ = _args[16];
lean_object* v___y_3983_ = _args[17];
lean_object* v___y_3984_ = _args[18];
lean_object* v___y_3985_ = _args[19];
lean_object* v___y_3986_ = _args[20];
_start:
{
uint8_t v___x_37476__boxed_3987_; uint8_t v___x_37482__boxed_3988_; uint8_t v___x_37485__boxed_3989_; lean_object* v_res_3990_; 
v___x_37476__boxed_3987_ = lean_unbox(v___x_3968_);
v___x_37482__boxed_3988_ = lean_unbox(v___x_3975_);
v___x_37485__boxed_3989_ = lean_unbox(v___x_3978_);
v_res_3990_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_3966_, v_otherwise_x3f_3967_, v___x_37476__boxed_3987_, v___x_3969_, v___x_3970_, v___x_3971_, v___x_3972_, v___x_3973_, v_dec_3974_, v___x_37482__boxed_3988_, v___y_3976_, v___x_3977_, v___x_37485__boxed_3989_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___x_3977_);
lean_dec(v_letOrReassign_3966_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4011_, lean_object* v_stx_4012_, lean_object* v_dec_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; uint8_t v___x_4026_; 
v___x_4022_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4023_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4024_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4025_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4012_);
v___x_4026_ = l_Lean_Syntax_isOfKind(v_stx_4012_, v___x_4025_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4012_);
v___x_4028_ = l_Lean_Syntax_isOfKind(v_stx_4012_, v___x_4027_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; 
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4029_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4029_;
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; 
v___x_4030_ = lean_unsigned_to_nat(0u);
v___x_4031_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4030_);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4031_);
v___x_4033_ = l_Lean_Syntax_isOfKind(v___x_4031_, v___x_4032_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4119_; lean_object* v_patType_x3f_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v___x_4119_ = lean_unsigned_to_nat(1u);
v___x_4150_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4119_);
v___x_4151_ = l_Lean_Syntax_isNone(v___x_4150_);
if (v___x_4151_ == 0)
{
uint8_t v___x_4152_; 
lean_inc(v___x_4150_);
v___x_4152_ = l_Lean_Syntax_matchesNull(v___x_4150_, v___x_4119_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec(v___x_4150_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4154_ = l_Lean_Syntax_getArg(v___x_4150_, v___x_4030_);
lean_dec(v___x_4150_);
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4154_);
v___x_4156_ = l_Lean_Syntax_isOfKind(v___x_4154_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
lean_dec(v___x_4154_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4157_;
}
else
{
lean_object* v_patType_x3f_4158_; lean_object* v___x_4159_; 
v_patType_x3f_4158_ = l_Lean_Syntax_getArg(v___x_4154_, v___x_4119_);
lean_dec(v___x_4154_);
v___x_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4159_, 0, v_patType_x3f_4158_);
v_patType_x3f_4121_ = v___x_4159_;
v___y_4122_ = v_a_4014_;
v___y_4123_ = v_a_4015_;
v___y_4124_ = v_a_4016_;
v___y_4125_ = v_a_4017_;
v___y_4126_ = v_a_4018_;
v___y_4127_ = v_a_4019_;
v___y_4128_ = v_a_4020_;
goto v___jp_4120_;
}
}
}
else
{
lean_object* v___x_4160_; 
lean_dec(v___x_4150_);
v___x_4160_ = lean_box(0);
v_patType_x3f_4121_ = v___x_4160_;
v___y_4122_ = v_a_4014_;
v___y_4123_ = v_a_4015_;
v___y_4124_ = v_a_4016_;
v___y_4125_ = v_a_4017_;
v___y_4126_ = v_a_4018_;
v___y_4127_ = v_a_4019_;
v___y_4128_ = v_a_4020_;
goto v___jp_4120_;
}
v___jp_4120_:
{
lean_object* v___x_4129_; lean_object* v_rhs_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4129_ = lean_unsigned_to_nat(3u);
v_rhs_4130_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4129_);
v___x_4131_ = lean_unsigned_to_nat(4u);
v___x_4132_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4131_);
lean_dec(v_stx_4012_);
v___x_4133_ = l_Lean_Syntax_isNone(v___x_4132_);
if (v___x_4133_ == 0)
{
uint8_t v___x_4134_; 
lean_inc(v___x_4132_);
v___x_4134_ = l_Lean_Syntax_matchesNull(v___x_4132_, v___x_4129_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; 
lean_dec(v___x_4132_);
lean_dec(v_rhs_4130_);
lean_dec(v_patType_x3f_4121_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_letOrReassign_4011_);
v___x_4135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4135_;
}
else
{
lean_object* v___x_4136_; lean_object* v_otherwise_x3f_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4136_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4137_ = l_Lean_Syntax_getArg(v___x_4132_, v___x_4119_);
v___x_4138_ = l_Lean_Syntax_getArg(v___x_4132_, v___x_4136_);
lean_dec(v___x_4132_);
v___x_4139_ = l_Lean_Syntax_getOptional_x3f(v___x_4138_);
lean_dec(v___x_4138_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_box(0);
v___y_4064_ = v___y_4123_;
v___y_4065_ = v___y_4125_;
v___y_4066_ = v_rhs_4130_;
v___y_4067_ = v___y_4127_;
v___y_4068_ = v___y_4124_;
v___y_4069_ = v___y_4126_;
v___y_4070_ = v_patType_x3f_4121_;
v___y_4071_ = v___y_4128_;
v___y_4072_ = v_otherwise_x3f_4137_;
v___y_4073_ = v___y_4122_;
v___y_4074_ = v___x_4140_;
goto v___jp_4063_;
}
else
{
lean_object* v_val_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
v_val_4141_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4139_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_val_4141_);
lean_dec(v___x_4139_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_val_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
v___y_4064_ = v___y_4123_;
v___y_4065_ = v___y_4125_;
v___y_4066_ = v_rhs_4130_;
v___y_4067_ = v___y_4127_;
v___y_4068_ = v___y_4124_;
v___y_4069_ = v___y_4126_;
v___y_4070_ = v_patType_x3f_4121_;
v___y_4071_ = v___y_4128_;
v___y_4072_ = v_otherwise_x3f_4137_;
v___y_4073_ = v___y_4122_;
v___y_4074_ = v___x_4146_;
goto v___jp_4063_;
}
}
}
}
}
else
{
lean_object* v___x_4149_; 
lean_dec(v___x_4132_);
v___x_4149_ = lean_box(0);
v___y_4035_ = v___y_4122_;
v___y_4036_ = v_patType_x3f_4121_;
v___y_4037_ = v___x_4149_;
v___y_4038_ = v___y_4123_;
v___y_4039_ = v___y_4124_;
v___y_4040_ = v_rhs_4130_;
v___y_4041_ = v___y_4126_;
v___y_4042_ = v___y_4127_;
v___y_4043_ = v___y_4128_;
v___y_4044_ = v___y_4125_;
v___y_4045_ = v___x_4149_;
goto v___jp_4034_;
}
}
}
else
{
lean_object* v_pattern_4161_; lean_object* v___x_4162_; lean_object* v_patType_x3f_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_pattern_4161_ = l_Lean_Syntax_getArg(v___x_4031_, v___x_4030_);
v___x_4162_ = lean_unsigned_to_nat(1u);
v___x_4209_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4162_);
v___x_4210_ = l_Lean_Syntax_isNone(v___x_4209_);
if (v___x_4210_ == 0)
{
uint8_t v___x_4211_; 
lean_inc(v___x_4209_);
v___x_4211_ = l_Lean_Syntax_matchesNull(v___x_4209_, v___x_4162_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; 
lean_dec(v___x_4209_);
lean_dec(v_pattern_4161_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4212_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4213_ = l_Lean_Syntax_getArg(v___x_4209_, v___x_4030_);
lean_dec(v___x_4209_);
v___x_4214_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4213_);
v___x_4215_ = l_Lean_Syntax_isOfKind(v___x_4213_, v___x_4214_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; 
lean_dec(v___x_4213_);
lean_dec(v_pattern_4161_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4216_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4216_;
}
else
{
lean_object* v_patType_x3f_4217_; lean_object* v___x_4218_; 
v_patType_x3f_4217_ = l_Lean_Syntax_getArg(v___x_4213_, v___x_4162_);
lean_dec(v___x_4213_);
v___x_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4218_, 0, v_patType_x3f_4217_);
v_patType_x3f_4164_ = v___x_4218_;
v___y_4165_ = v_a_4014_;
v___y_4166_ = v_a_4015_;
v___y_4167_ = v_a_4016_;
v___y_4168_ = v_a_4017_;
v___y_4169_ = v_a_4018_;
v___y_4170_ = v_a_4019_;
v___y_4171_ = v_a_4020_;
goto v___jp_4163_;
}
}
}
else
{
lean_object* v___x_4219_; 
lean_dec(v___x_4209_);
v___x_4219_ = lean_box(0);
v_patType_x3f_4164_ = v___x_4219_;
v___y_4165_ = v_a_4014_;
v___y_4166_ = v_a_4015_;
v___y_4167_ = v_a_4016_;
v___y_4168_ = v_a_4017_;
v___y_4169_ = v_a_4018_;
v___y_4170_ = v_a_4019_;
v___y_4171_ = v_a_4020_;
goto v___jp_4163_;
}
v___jp_4163_:
{
lean_object* v___x_4172_; lean_object* v_rhs_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4172_ = lean_unsigned_to_nat(3u);
v_rhs_4173_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4172_);
v___x_4174_ = lean_unsigned_to_nat(4u);
v___x_4175_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4174_);
lean_dec(v_stx_4012_);
lean_inc(v___x_4175_);
v___x_4176_ = l_Lean_Syntax_matchesNull(v___x_4175_, v___x_4030_);
if (v___x_4176_ == 0)
{
uint8_t v___x_4177_; 
lean_dec(v_pattern_4161_);
v___x_4177_ = l_Lean_Syntax_isNone(v___x_4175_);
if (v___x_4177_ == 0)
{
uint8_t v___x_4178_; 
lean_inc(v___x_4175_);
v___x_4178_ = l_Lean_Syntax_matchesNull(v___x_4175_, v___x_4172_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; 
lean_dec(v___x_4175_);
lean_dec(v_rhs_4173_);
lean_dec(v_patType_x3f_4164_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_letOrReassign_4011_);
v___x_4179_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4179_;
}
else
{
lean_object* v___x_4180_; lean_object* v_otherwise_x3f_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4181_ = l_Lean_Syntax_getArg(v___x_4175_, v___x_4162_);
v___x_4182_ = l_Lean_Syntax_getArg(v___x_4175_, v___x_4180_);
lean_dec(v___x_4175_);
v___x_4183_ = l_Lean_Syntax_getOptional_x3f(v___x_4182_);
lean_dec(v___x_4182_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_box(0);
v___y_4107_ = v_rhs_4173_;
v___y_4108_ = v___y_4167_;
v___y_4109_ = v___y_4171_;
v___y_4110_ = v___y_4168_;
v___y_4111_ = v_patType_x3f_4164_;
v___y_4112_ = v___y_4170_;
v___y_4113_ = v___y_4169_;
v___y_4114_ = v___y_4166_;
v___y_4115_ = v___y_4165_;
v___y_4116_ = v_otherwise_x3f_4181_;
v___y_4117_ = v___x_4184_;
goto v___jp_4106_;
}
else
{
lean_object* v_val_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
v_val_4185_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4183_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_val_4185_);
lean_dec(v___x_4183_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_val_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
v___y_4107_ = v_rhs_4173_;
v___y_4108_ = v___y_4167_;
v___y_4109_ = v___y_4171_;
v___y_4110_ = v___y_4168_;
v___y_4111_ = v_patType_x3f_4164_;
v___y_4112_ = v___y_4170_;
v___y_4113_ = v___y_4169_;
v___y_4114_ = v___y_4166_;
v___y_4115_ = v___y_4165_;
v___y_4116_ = v_otherwise_x3f_4181_;
v___y_4117_ = v___x_4190_;
goto v___jp_4106_;
}
}
}
}
}
else
{
lean_object* v___x_4193_; 
lean_dec(v___x_4175_);
v___x_4193_ = lean_box(0);
v___y_4077_ = v___y_4171_;
v___y_4078_ = v___y_4169_;
v___y_4079_ = v_rhs_4173_;
v___y_4080_ = v___y_4167_;
v___y_4081_ = v___x_4193_;
v___y_4082_ = v___y_4165_;
v___y_4083_ = v_patType_x3f_4164_;
v___y_4084_ = v___y_4168_;
v___y_4085_ = v___y_4166_;
v___y_4086_ = v___y_4170_;
v___y_4087_ = v___x_4193_;
goto v___jp_4076_;
}
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_dec(v___x_4175_);
lean_dec(v___x_4031_);
lean_dec(v_letOrReassign_4011_);
v___x_4194_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4195_ = l_Lean_Core_mkFreshUserName(v___x_4194_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; uint8_t v_kind_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4195_);
v_kind_4197_ = lean_ctor_get_uint8(v_dec_4013_, sizeof(void*)*3);
v___x_4198_ = l_Lean_mkIdentFrom(v_pattern_4161_, v_a_4196_, v___x_4026_);
lean_dec(v_pattern_4161_);
v___x_4199_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4199_, 0, v_dec_4013_);
lean_inc_ref(v___y_4168_);
v___x_4200_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4198_, v_patType_x3f_4164_, v_rhs_4173_, v___x_4199_, v_kind_4197_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4200_;
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_rhs_4173_);
lean_dec(v_patType_x3f_4164_);
lean_dec(v_pattern_4161_);
lean_dec_ref(v_dec_4013_);
v_a_4201_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4195_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4195_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
}
v___jp_4034_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4047_ = l_Lean_Core_mkFreshUserName(v___x_4046_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___y_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref(v___x_4047_);
v___x_4049_ = l_Lean_mkIdentFrom(v___x_4031_, v_a_4048_, v___x_4033_);
v___x_4050_ = lean_box(v___x_4033_);
v___x_4051_ = lean_box(v___x_4028_);
lean_inc(v___x_4049_);
v___y_4052_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4052_, 0, v_letOrReassign_4011_);
lean_closure_set(v___y_4052_, 1, v___y_4037_);
lean_closure_set(v___y_4052_, 2, v___x_4050_);
lean_closure_set(v___y_4052_, 3, v___x_4022_);
lean_closure_set(v___y_4052_, 4, v___x_4023_);
lean_closure_set(v___y_4052_, 5, v___x_4024_);
lean_closure_set(v___y_4052_, 6, v___x_4031_);
lean_closure_set(v___y_4052_, 7, v___x_4049_);
lean_closure_set(v___y_4052_, 8, v_dec_4013_);
lean_closure_set(v___y_4052_, 9, v___x_4051_);
lean_closure_set(v___y_4052_, 10, v___y_4045_);
lean_closure_set(v___y_4052_, 11, v___x_4030_);
v___x_4053_ = 0;
lean_inc_ref(v___y_4044_);
v___x_4054_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4049_, v___y_4036_, v___y_4040_, v___y_4052_, v___x_4053_, v___y_4035_, v___y_4038_, v___y_4039_, v___y_4044_, v___y_4041_, v___y_4042_, v___y_4043_);
return v___x_4054_;
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v___y_4045_);
lean_dec(v___y_4040_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_letOrReassign_4011_);
v_a_4055_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4047_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4047_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
v___jp_4063_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___y_4072_);
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4070_;
v___y_4037_ = v___x_4075_;
v___y_4038_ = v___y_4064_;
v___y_4039_ = v___y_4068_;
v___y_4040_ = v___y_4066_;
v___y_4041_ = v___y_4069_;
v___y_4042_ = v___y_4067_;
v___y_4043_ = v___y_4071_;
v___y_4044_ = v___y_4065_;
v___y_4045_ = v___y_4074_;
goto v___jp_4034_;
}
v___jp_4076_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4089_ = l_Lean_Core_mkFreshUserName(v___x_4088_, v___y_4086_, v___y_4077_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___y_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref(v___x_4089_);
v___x_4091_ = l_Lean_mkIdentFrom(v___x_4031_, v_a_4090_, v___x_4026_);
v___x_4092_ = lean_box(v___x_4026_);
v___x_4093_ = lean_box(v___x_4028_);
v___x_4094_ = lean_box(v___x_4033_);
lean_inc(v___x_4091_);
v___y_4095_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4095_, 0, v_letOrReassign_4011_);
lean_closure_set(v___y_4095_, 1, v___y_4081_);
lean_closure_set(v___y_4095_, 2, v___x_4092_);
lean_closure_set(v___y_4095_, 3, v___x_4022_);
lean_closure_set(v___y_4095_, 4, v___x_4023_);
lean_closure_set(v___y_4095_, 5, v___x_4024_);
lean_closure_set(v___y_4095_, 6, v___x_4031_);
lean_closure_set(v___y_4095_, 7, v___x_4091_);
lean_closure_set(v___y_4095_, 8, v_dec_4013_);
lean_closure_set(v___y_4095_, 9, v___x_4093_);
lean_closure_set(v___y_4095_, 10, v___y_4087_);
lean_closure_set(v___y_4095_, 11, v___x_4030_);
lean_closure_set(v___y_4095_, 12, v___x_4094_);
v___x_4096_ = 0;
lean_inc_ref(v___y_4084_);
v___x_4097_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4091_, v___y_4083_, v___y_4079_, v___y_4095_, v___x_4096_, v___y_4082_, v___y_4085_, v___y_4080_, v___y_4084_, v___y_4078_, v___y_4086_, v___y_4077_);
return v___x_4097_;
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v___y_4087_);
lean_dec(v___y_4083_);
lean_dec(v___y_4081_);
lean_dec(v___y_4079_);
lean_dec(v___x_4031_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_letOrReassign_4011_);
v_a_4098_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4089_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4089_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
v___jp_4106_:
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___y_4116_);
v___y_4077_ = v___y_4109_;
v___y_4078_ = v___y_4113_;
v___y_4079_ = v___y_4107_;
v___y_4080_ = v___y_4108_;
v___y_4081_ = v___x_4118_;
v___y_4082_ = v___y_4115_;
v___y_4083_ = v___y_4111_;
v___y_4084_ = v___y_4110_;
v___y_4085_ = v___y_4114_;
v___y_4086_ = v___y_4112_;
v___y_4087_ = v___y_4117_;
goto v___jp_4076_;
}
}
}
else
{
lean_object* v___x_4220_; lean_object* v_x_4221_; lean_object* v___y_4223_; lean_object* v_xType_x3f_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v_xType_x3f_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___x_4283_; uint8_t v___x_4284_; 
v___x_4220_ = lean_unsigned_to_nat(0u);
v_x_4221_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4220_);
v___x_4283_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4221_);
v___x_4284_ = l_Lean_Syntax_isOfKind(v_x_4221_, v___x_4283_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; 
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4285_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v___x_4286_ = lean_unsigned_to_nat(1u);
v___x_4287_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4286_);
v___x_4288_ = l_Lean_Syntax_isNone(v___x_4287_);
if (v___x_4288_ == 0)
{
uint8_t v___x_4289_; 
lean_inc(v___x_4287_);
v___x_4289_ = l_Lean_Syntax_matchesNull(v___x_4287_, v___x_4286_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; 
lean_dec(v___x_4287_);
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4290_;
}
else
{
lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4291_ = l_Lean_Syntax_getArg(v___x_4287_, v___x_4220_);
lean_dec(v___x_4287_);
v___x_4292_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4291_);
v___x_4293_ = l_Lean_Syntax_isOfKind(v___x_4291_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; 
lean_dec(v___x_4291_);
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v___x_4294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4294_;
}
else
{
lean_object* v_xType_x3f_4295_; lean_object* v___x_4296_; 
v_xType_x3f_4295_ = l_Lean_Syntax_getArg(v___x_4291_, v___x_4286_);
lean_dec(v___x_4291_);
v___x_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_xType_x3f_4295_);
v_xType_x3f_4238_ = v___x_4296_;
v___y_4239_ = v_a_4014_;
v___y_4240_ = v_a_4015_;
v___y_4241_ = v_a_4016_;
v___y_4242_ = v_a_4017_;
v___y_4243_ = v_a_4018_;
v___y_4244_ = v_a_4019_;
v___y_4245_ = v_a_4020_;
goto v___jp_4237_;
}
}
}
else
{
lean_object* v___x_4297_; 
lean_dec(v___x_4287_);
v___x_4297_ = lean_box(0);
v_xType_x3f_4238_ = v___x_4297_;
v___y_4239_ = v_a_4014_;
v___y_4240_ = v_a_4015_;
v___y_4241_ = v_a_4016_;
v___y_4242_ = v_a_4017_;
v___y_4243_ = v_a_4018_;
v___y_4244_ = v_a_4019_;
v___y_4245_ = v_a_4020_;
goto v___jp_4237_;
}
}
v___jp_4222_:
{
uint8_t v_kind_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_kind_4232_ = lean_ctor_get_uint8(v_dec_4013_, sizeof(void*)*3);
v___x_4233_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4011_);
lean_dec(v_letOrReassign_4011_);
v___x_4234_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4234_, 0, v_dec_4013_);
lean_inc(v_x_4221_);
v___x_4235_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4235_, 0, lean_box(0));
lean_closure_set(v___x_4235_, 1, v___x_4233_);
lean_closure_set(v___x_4235_, 2, v_x_4221_);
lean_closure_set(v___x_4235_, 3, v___x_4234_);
lean_inc_ref(v___y_4228_);
v___x_4236_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4221_, v_xType_x3f_4224_, v___y_4223_, v___x_4235_, v_kind_4232_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
return v___x_4236_;
}
v___jp_4237_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_mk_empty_array_with_capacity(v___x_4246_);
lean_inc(v_x_4221_);
v___x_4248_ = lean_array_push(v___x_4247_, v_x_4221_);
v___x_4249_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4011_, v___x_4248_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec_ref(v___x_4248_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___x_4250_; lean_object* v_rhs_4251_; 
lean_dec_ref(v___x_4249_);
v___x_4250_ = lean_unsigned_to_nat(3u);
v_rhs_4251_ = l_Lean_Syntax_getArg(v_stx_4012_, v___x_4250_);
lean_dec(v_stx_4012_);
if (lean_obj_tag(v_letOrReassign_4011_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4238_) == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = l_Lean_TSyntax_getId(v_x_4221_);
v___x_4253_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4252_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = l_Lean_LocalDecl_type(v_a_4254_);
lean_dec(v_a_4254_);
v___x_4256_ = l_Lean_Elab_Term_exprToSyntax(v___x_4255_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4258_, 0, v_a_4257_);
v___y_4223_ = v_rhs_4251_;
v_xType_x3f_4224_ = v___x_4258_;
v___y_4225_ = v___y_4239_;
v___y_4226_ = v___y_4240_;
v___y_4227_ = v___y_4241_;
v___y_4228_ = v___y_4242_;
v___y_4229_ = v___y_4243_;
v___y_4230_ = v___y_4244_;
v___y_4231_ = v___y_4245_;
goto v___jp_4222_;
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v_rhs_4251_);
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
v_a_4259_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4256_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4256_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v_rhs_4251_);
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
v_a_4267_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4253_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4253_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
v___y_4223_ = v_rhs_4251_;
v_xType_x3f_4224_ = v_xType_x3f_4238_;
v___y_4225_ = v___y_4239_;
v___y_4226_ = v___y_4240_;
v___y_4227_ = v___y_4241_;
v___y_4228_ = v___y_4242_;
v___y_4229_ = v___y_4243_;
v___y_4230_ = v___y_4244_;
v___y_4231_ = v___y_4245_;
goto v___jp_4222_;
}
}
else
{
v___y_4223_ = v_rhs_4251_;
v_xType_x3f_4224_ = v_xType_x3f_4238_;
v___y_4225_ = v___y_4239_;
v___y_4226_ = v___y_4240_;
v___y_4227_ = v___y_4241_;
v___y_4228_ = v___y_4242_;
v___y_4229_ = v___y_4243_;
v___y_4230_ = v___y_4244_;
v___y_4231_ = v___y_4245_;
goto v___jp_4222_;
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_xType_x3f_4238_);
lean_dec(v_x_4221_);
lean_dec_ref(v_dec_4013_);
lean_dec(v_stx_4012_);
lean_dec(v_letOrReassign_4011_);
v_a_4275_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4249_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4249_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4298_, lean_object* v_stx_4299_, lean_object* v_dec_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4298_, v_stx_4299_, v_dec_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_);
lean_dec(v_a_4307_);
lean_dec_ref(v_a_4306_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4315_, lean_object* v_dec_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_mutTk_x3f_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4315_);
v___x_4342_ = l_Lean_Syntax_isOfKind(v_stx_4315_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; 
lean_dec_ref(v_dec_4316_);
lean_dec(v_stx_4315_);
v___x_4343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4344_ = lean_unsigned_to_nat(1u);
v___x_4345_ = l_Lean_Syntax_getArg(v_stx_4315_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_isNone(v___x_4345_);
if (v___x_4346_ == 0)
{
uint8_t v___x_4347_; 
lean_inc(v___x_4345_);
v___x_4347_ = l_Lean_Syntax_matchesNull(v___x_4345_, v___x_4344_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; 
lean_dec(v___x_4345_);
lean_dec_ref(v_dec_4316_);
lean_dec(v_stx_4315_);
v___x_4348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; lean_object* v_mutTk_x3f_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_4350_ = l_Lean_Syntax_getArg(v___x_4345_, v___x_4349_);
lean_dec(v___x_4345_);
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_mutTk_x3f_4350_);
v_mutTk_x3f_4326_ = v___x_4351_;
v___y_4327_ = v_a_4317_;
v___y_4328_ = v_a_4318_;
v___y_4329_ = v_a_4319_;
v___y_4330_ = v_a_4320_;
v___y_4331_ = v_a_4321_;
v___y_4332_ = v_a_4322_;
v___y_4333_ = v_a_4323_;
goto v___jp_4325_;
}
}
else
{
lean_object* v___x_4352_; 
lean_dec(v___x_4345_);
v___x_4352_ = lean_box(0);
v_mutTk_x3f_4326_ = v___x_4352_;
v___y_4327_ = v_a_4317_;
v___y_4328_ = v_a_4318_;
v___y_4329_ = v_a_4319_;
v___y_4330_ = v_a_4320_;
v___y_4331_ = v_a_4321_;
v___y_4332_ = v_a_4322_;
v___y_4333_ = v_a_4323_;
goto v___jp_4325_;
}
}
v___jp_4325_:
{
lean_object* v___x_4334_; lean_object* v_decl_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4334_ = lean_unsigned_to_nat(2u);
v_decl_4335_ = l_Lean_Syntax_getArg(v_stx_4315_, v___x_4334_);
lean_dec(v_stx_4315_);
v___x_4336_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4335_);
v___x_4337_ = l_Lean_Syntax_isOfKind(v_decl_4335_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec(v_decl_4335_);
lean_dec(v_mutTk_x3f_4326_);
lean_dec_ref(v_dec_4316_);
v___x_4338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v_mutTk_x3f_4326_);
lean_inc_ref(v___y_4327_);
v___x_4340_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4339_, v_decl_4335_, v_dec_4316_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
return v___x_4340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4353_, lean_object* v_dec_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_Elab_Do_elabDoLet(v_stx_4353_, v_dec_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec_ref(v_a_4355_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4371_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4372_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4374_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4375_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4371_, v___x_4372_, v___x_4373_, v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4383_, lean_object* v_dec_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v___x_4393_; uint8_t v___x_4394_; 
v___x_4393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4383_);
v___x_4394_ = l_Lean_Syntax_isOfKind(v_stx_4383_, v___x_4393_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; 
lean_dec_ref(v_dec_4384_);
lean_dec(v_stx_4383_);
v___x_4395_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4395_;
}
else
{
lean_object* v___x_4396_; lean_object* v_decl_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4396_ = lean_unsigned_to_nat(1u);
v_decl_4397_ = l_Lean_Syntax_getArg(v_stx_4383_, v___x_4396_);
lean_dec(v_stx_4383_);
v___x_4398_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4397_);
v___x_4399_ = l_Lean_Syntax_isOfKind(v_decl_4397_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; 
lean_dec(v_decl_4397_);
lean_dec_ref(v_dec_4384_);
v___x_4400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4400_;
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_box(1);
lean_inc_ref(v_a_4385_);
v___x_4402_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4401_, v_decl_4397_, v_dec_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
return v___x_4402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4403_, lean_object* v_dec_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_Elab_Do_elabDoHave(v_stx_4403_, v_dec_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec_ref(v_a_4405_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4421_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4422_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4423_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4424_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4425_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4421_, v___x_4422_, v___x_4423_, v___x_4424_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4430_, lean_object* v___x_4431_, lean_object* v___x_4432_, lean_object* v___x_4433_, lean_object* v_decls_4434_, lean_object* v_a_4435_, uint8_t v___x_4436_, lean_object* v_body_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_ref_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_ref_4446_ = lean_ctor_get(v___y_4443_, 5);
v___x_4447_ = 0;
v___x_4448_ = l_Lean_SourceInfo_fromRef(v_ref_4446_, v___x_4447_);
v___x_4449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4450_ = l_Lean_Name_mkStr4(v___x_4430_, v___x_4431_, v___x_4432_, v___x_4449_);
v___x_4451_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4448_);
v___x_4452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4448_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
v___x_4453_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
lean_inc(v___x_4448_);
v___x_4454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4448_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
lean_inc(v___x_4448_);
v___x_4455_ = l_Lean_Syntax_node2(v___x_4448_, v___x_4433_, v___x_4452_, v___x_4454_);
v___x_4456_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4448_);
v___x_4457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4448_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
v___x_4458_ = l_Lean_Syntax_node4(v___x_4448_, v___x_4450_, v___x_4455_, v_decls_4434_, v___x_4457_, v_body_4437_);
v___x_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_a_4435_);
v___x_4460_ = l_Lean_Elab_Term_elabTerm(v___x_4458_, v___x_4459_, v___x_4436_, v___x_4436_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4461_, lean_object* v___x_4462_, lean_object* v___x_4463_, lean_object* v___x_4464_, lean_object* v_decls_4465_, lean_object* v_a_4466_, lean_object* v___x_4467_, lean_object* v_body_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v___x_4790__boxed_4477_; lean_object* v_res_4478_; 
v___x_4790__boxed_4477_ = lean_unbox(v___x_4467_);
v_res_4478_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4461_, v___x_4462_, v___x_4463_, v___x_4464_, v_decls_4465_, v_a_4466_, v___x_4790__boxed_4477_, v_body_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec_ref(v___y_4469_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
if (lean_obj_tag(v_a_4479_) == 0)
{
lean_object* v___x_4481_; 
v___x_4481_ = l_List_reverse___redArg(v_a_4480_);
return v___x_4481_;
}
else
{
lean_object* v_head_4482_; lean_object* v_tail_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4492_; 
v_head_4482_ = lean_ctor_get(v_a_4479_, 0);
v_tail_4483_ = lean_ctor_get(v_a_4479_, 1);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_a_4479_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4485_ = v_a_4479_;
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_tail_4483_);
lean_inc(v_head_4482_);
lean_dec(v_a_4479_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = l_Lean_MessageData_ofSyntax(v_head_4482_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v_a_4480_);
lean_ctor_set(v___x_4485_, 0, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4487_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_a_4480_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
v_a_4479_ = v_tail_4483_;
v_a_4480_ = v___x_4489_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4510_ = l_Lean_stringToMessageData(v___x_4509_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4511_, lean_object* v_dec_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4522_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4523_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4511_);
v___x_4525_ = l_Lean_Syntax_isOfKind(v_stx_4511_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; 
lean_dec_ref(v_a_4513_);
lean_dec_ref(v_dec_4512_);
lean_dec(v_stx_4511_);
v___x_4526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4526_;
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4527_);
v___x_4529_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
v___x_4530_ = l_Lean_Syntax_isOfKind(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_dec_ref(v_a_4513_);
lean_dec_ref(v_dec_4512_);
lean_dec(v_stx_4511_);
v___x_4531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; lean_object* v_decls_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4532_ = lean_unsigned_to_nat(1u);
v_decls_4533_ = l_Lean_Syntax_getArg(v_stx_4511_, v___x_4532_);
lean_dec(v_stx_4511_);
v___x_4534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4533_);
v___x_4535_ = l_Lean_Syntax_isOfKind(v_decls_4533_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; 
lean_dec(v_decls_4533_);
lean_dec_ref(v_a_4513_);
lean_dec_ref(v_dec_4512_);
v___x_4536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4536_;
}
else
{
lean_object* v___x_4537_; 
lean_inc(v_decls_4533_);
v___x_4537_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4533_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v_doBlockResultType_4539_; lean_object* v___x_4540_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref(v___x_4537_);
v_doBlockResultType_4539_ = lean_ctor_get(v_a_4513_, 3);
lean_inc_ref(v_a_4513_);
lean_inc_ref(v_doBlockResultType_4539_);
v___x_4540_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_4539_, v_a_4513_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4542_; lean_object* v___f_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref(v___x_4540_);
v___x_4542_ = lean_box(v___x_4535_);
v___f_4543_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4543_, 0, v___x_4521_);
lean_closure_set(v___f_4543_, 1, v___x_4522_);
lean_closure_set(v___f_4543_, 2, v___x_4523_);
lean_closure_set(v___f_4543_, 3, v___x_4529_);
lean_closure_set(v___f_4543_, 4, v_decls_4533_);
lean_closure_set(v___f_4543_, 5, v_a_4541_);
lean_closure_set(v___f_4543_, 6, v___x_4542_);
v___x_4544_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4545_ = lean_array_to_list(v_a_4538_);
v___x_4546_ = lean_box(0);
v___x_4547_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4545_, v___x_4546_);
v___x_4548_ = l_Lean_MessageData_ofList(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4544_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
v___x_4550_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4550_, 0, v_dec_4512_);
v___x_4551_ = lean_box(0);
v___x_4552_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4549_, v___x_4550_, v___f_4543_, v___x_4551_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec_ref(v_a_4513_);
return v___x_4552_;
}
else
{
lean_dec(v_a_4538_);
lean_dec(v_decls_4533_);
lean_dec_ref(v_a_4513_);
lean_dec_ref(v_dec_4512_);
return v___x_4540_;
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v_decls_4533_);
lean_dec_ref(v_a_4513_);
lean_dec_ref(v_dec_4512_);
v_a_4553_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4537_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4537_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4561_, lean_object* v_dec_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4561_, v_dec_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4579_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4581_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4582_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4583_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4579_, v___x_4580_, v___x_4581_, v___x_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4599_, lean_object* v_dec_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4599_);
v___x_4639_ = l_Lean_Syntax_isOfKind(v_stx_4599_, v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
lean_dec_ref(v_dec_4600_);
lean_dec(v_stx_4599_);
v___x_4640_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4641_ = lean_unsigned_to_nat(0u);
v___x_4642_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4641_);
lean_dec(v_stx_4599_);
v___x_4643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_4642_);
v___x_4644_ = l_Lean_Syntax_isOfKind(v___x_4642_, v___x_4643_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; uint8_t v___x_4646_; 
v___x_4645_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_4642_);
v___x_4646_ = l_Lean_Syntax_isOfKind(v___x_4642_, v___x_4645_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; 
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4647_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4647_;
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v_decl_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4648_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4649_ = lean_unsigned_to_nat(1u);
v___x_4650_ = lean_mk_empty_array_with_capacity(v___x_4649_);
v___x_4651_ = lean_array_push(v___x_4650_, v___x_4642_);
v___x_4652_ = lean_box(2);
v_decl_4653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_4653_, 0, v___x_4652_);
lean_ctor_set(v_decl_4653_, 1, v___x_4648_);
lean_ctor_set(v_decl_4653_, 2, v___x_4651_);
v___x_4654_ = lean_box(2);
lean_inc_ref(v_a_4601_);
v___x_4655_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4654_, v_decl_4653_, v_dec_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
return v___x_4655_;
}
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v___x_4656_ = l_Lean_Syntax_getArg(v___x_4642_, v___x_4641_);
v___x_4657_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4656_);
v___x_4658_ = l_Lean_Syntax_isOfKind(v___x_4656_, v___x_4657_);
if (v___x_4658_ == 0)
{
lean_object* v___x_4659_; 
lean_dec(v___x_4656_);
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4659_;
}
else
{
lean_object* v___x_4660_; lean_object* v_xType_x3f_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v___x_4660_ = l_Lean_Syntax_getArg(v___x_4656_, v___x_4641_);
lean_dec(v___x_4656_);
v___x_4687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4660_);
v___x_4688_ = l_Lean_Syntax_isOfKind(v___x_4660_, v___x_4687_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4689_; 
lean_dec(v___x_4660_);
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4689_;
}
else
{
lean_object* v___x_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4690_ = lean_unsigned_to_nat(1u);
v___x_4691_ = l_Lean_Syntax_getArg(v___x_4642_, v___x_4690_);
v___x_4692_ = l_Lean_Syntax_matchesNull(v___x_4691_, v___x_4641_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
lean_dec(v___x_4660_);
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4693_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4693_;
}
else
{
lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4694_ = lean_unsigned_to_nat(2u);
v___x_4695_ = l_Lean_Syntax_getArg(v___x_4642_, v___x_4694_);
v___x_4696_ = l_Lean_Syntax_isNone(v___x_4695_);
if (v___x_4696_ == 0)
{
uint8_t v___x_4697_; 
lean_inc(v___x_4695_);
v___x_4697_ = l_Lean_Syntax_matchesNull(v___x_4695_, v___x_4690_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; 
lean_dec(v___x_4695_);
lean_dec(v___x_4660_);
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4698_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4698_;
}
else
{
lean_object* v___x_4699_; lean_object* v___x_4700_; uint8_t v___x_4701_; 
v___x_4699_ = l_Lean_Syntax_getArg(v___x_4695_, v___x_4641_);
lean_dec(v___x_4695_);
v___x_4700_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4699_);
v___x_4701_ = l_Lean_Syntax_isOfKind(v___x_4699_, v___x_4700_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; 
lean_dec(v___x_4699_);
lean_dec(v___x_4660_);
lean_dec(v___x_4642_);
lean_dec_ref(v_dec_4600_);
v___x_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4702_;
}
else
{
lean_object* v_xType_x3f_4703_; lean_object* v___x_4704_; 
v_xType_x3f_4703_ = l_Lean_Syntax_getArg(v___x_4699_, v___x_4690_);
lean_dec(v___x_4699_);
v___x_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4704_, 0, v_xType_x3f_4703_);
v_xType_x3f_4662_ = v___x_4704_;
v___y_4663_ = v_a_4601_;
v___y_4664_ = v_a_4602_;
v___y_4665_ = v_a_4603_;
v___y_4666_ = v_a_4604_;
v___y_4667_ = v_a_4605_;
v___y_4668_ = v_a_4606_;
v___y_4669_ = v_a_4607_;
goto v___jp_4661_;
}
}
}
else
{
lean_object* v___x_4705_; 
lean_dec(v___x_4695_);
v___x_4705_ = lean_box(0);
v_xType_x3f_4662_ = v___x_4705_;
v___y_4663_ = v_a_4601_;
v___y_4664_ = v_a_4602_;
v___y_4665_ = v_a_4603_;
v___y_4666_ = v_a_4604_;
v___y_4667_ = v_a_4605_;
v___y_4668_ = v_a_4606_;
v___y_4669_ = v_a_4607_;
goto v___jp_4661_;
}
}
}
v___jp_4661_:
{
lean_object* v_ref_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_ref_4670_ = lean_ctor_get(v___y_4668_, 5);
v___x_4671_ = lean_unsigned_to_nat(4u);
v___x_4672_ = l_Lean_Syntax_getArg(v___x_4642_, v___x_4671_);
lean_dec(v___x_4642_);
v___x_4673_ = 0;
v___x_4674_ = l_Lean_SourceInfo_fromRef(v_ref_4670_, v___x_4673_);
v___x_4675_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_4674_);
v___x_4676_ = l_Lean_Syntax_node1(v___x_4674_, v___x_4657_, v___x_4660_);
v___x_4677_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4678_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4674_);
v___x_4679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4674_);
lean_ctor_set(v___x_4679_, 1, v___x_4677_);
lean_ctor_set(v___x_4679_, 2, v___x_4678_);
if (lean_obj_tag(v_xType_x3f_4662_) == 1)
{
lean_object* v_val_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v_val_4680_ = lean_ctor_get(v_xType_x3f_4662_, 0);
lean_inc(v_val_4680_);
lean_dec_ref(v_xType_x3f_4662_);
v___x_4681_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4682_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc(v___x_4674_);
v___x_4683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4674_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
lean_inc(v___x_4674_);
v___x_4684_ = l_Lean_Syntax_node2(v___x_4674_, v___x_4681_, v___x_4683_, v_val_4680_);
v___x_4685_ = l_Array_mkArray1___redArg(v___x_4684_);
v___y_4610_ = v___y_4663_;
v___y_4611_ = v___y_4666_;
v___y_4612_ = v___y_4669_;
v___y_4613_ = v___x_4677_;
v___y_4614_ = v___x_4679_;
v___y_4615_ = v___x_4672_;
v___y_4616_ = v___x_4678_;
v___y_4617_ = v___x_4675_;
v___y_4618_ = v___x_4674_;
v___y_4619_ = v___y_4667_;
v___y_4620_ = v___y_4668_;
v___y_4621_ = v___x_4676_;
v___y_4622_ = v___y_4664_;
v___y_4623_ = v___y_4665_;
v___y_4624_ = v___x_4685_;
goto v___jp_4609_;
}
else
{
lean_object* v___x_4686_; 
lean_dec(v_xType_x3f_4662_);
v___x_4686_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4610_ = v___y_4663_;
v___y_4611_ = v___y_4666_;
v___y_4612_ = v___y_4669_;
v___y_4613_ = v___x_4677_;
v___y_4614_ = v___x_4679_;
v___y_4615_ = v___x_4672_;
v___y_4616_ = v___x_4678_;
v___y_4617_ = v___x_4675_;
v___y_4618_ = v___x_4674_;
v___y_4619_ = v___y_4667_;
v___y_4620_ = v___y_4668_;
v___y_4621_ = v___x_4676_;
v___y_4622_ = v___y_4664_;
v___y_4623_ = v___y_4665_;
v___y_4624_ = v___x_4686_;
goto v___jp_4609_;
}
}
}
}
}
v___jp_4609_:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4625_ = l_Array_append___redArg(v___y_4616_, v___y_4624_);
lean_dec_ref(v___y_4624_);
lean_inc(v___y_4618_);
v___x_4626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4626_, 0, v___y_4618_);
lean_ctor_set(v___x_4626_, 1, v___y_4613_);
lean_ctor_set(v___x_4626_, 2, v___x_4625_);
v___x_4627_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___y_4618_);
v___x_4628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___y_4618_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = l_Lean_Syntax_node5(v___y_4618_, v___y_4617_, v___y_4621_, v___y_4614_, v___x_4626_, v___x_4628_, v___y_4615_);
v___x_4630_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4631_ = lean_unsigned_to_nat(1u);
v___x_4632_ = lean_mk_empty_array_with_capacity(v___x_4631_);
v___x_4633_ = lean_array_push(v___x_4632_, v___x_4629_);
v___x_4634_ = lean_box(2);
v___x_4635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
lean_ctor_set(v___x_4635_, 1, v___x_4630_);
lean_ctor_set(v___x_4635_, 2, v___x_4633_);
v___x_4636_ = lean_box(2);
lean_inc_ref(v___y_4610_);
v___x_4637_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4636_, v___x_4635_, v_dec_4600_, v___y_4610_, v___y_4622_, v___y_4623_, v___y_4611_, v___y_4619_, v___y_4620_, v___y_4612_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_4706_, lean_object* v_dec_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Lean_Elab_Do_elabDoReassign(v_stx_4706_, v_dec_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec_ref(v_a_4708_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4724_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4725_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_4726_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_4727_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_4728_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4724_, v___x_4725_, v___x_4726_, v___x_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_4750_, size_t v_sz_4751_, size_t v_i_4752_, lean_object* v_b_4753_, lean_object* v___y_4754_){
_start:
{
uint8_t v___x_4756_; 
v___x_4756_ = lean_usize_dec_lt(v_i_4752_, v_sz_4751_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v_b_4753_);
return v___x_4757_;
}
else
{
lean_object* v_ref_4758_; lean_object* v___x_4759_; lean_object* v_a_4760_; uint8_t v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; size_t v___x_4793_; size_t v___x_4794_; 
v_ref_4758_ = lean_ctor_get(v___y_4754_, 5);
v___x_4759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4760_ = lean_array_uget_borrowed(v_as_4750_, v_i_4752_);
v___x_4761_ = 0;
v___x_4762_ = l_Lean_SourceInfo_fromRef(v_ref_4758_, v___x_4761_);
v___x_4763_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4765_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4766_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4762_);
v___x_4767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4762_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc(v___x_4762_);
v___x_4769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4762_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
lean_inc(v___x_4762_);
v___x_4770_ = l_Lean_Syntax_node1(v___x_4762_, v___x_4763_, v___x_4769_);
v___x_4771_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4772_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4773_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v_a_4760_);
lean_inc(v___x_4762_);
v___x_4774_ = l_Lean_Syntax_node1(v___x_4762_, v___x_4773_, v_a_4760_);
v___x_4775_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4762_);
v___x_4776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4762_);
lean_ctor_set(v___x_4776_, 1, v___x_4763_);
lean_ctor_set(v___x_4776_, 2, v___x_4775_);
v___x_4777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_4762_);
v___x_4778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4762_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
lean_inc(v_a_4760_);
lean_inc_ref_n(v___x_4776_, 2);
lean_inc(v___x_4762_);
v___x_4779_ = l_Lean_Syntax_node5(v___x_4762_, v___x_4772_, v___x_4774_, v___x_4776_, v___x_4776_, v___x_4778_, v_a_4760_);
lean_inc(v___x_4762_);
v___x_4780_ = l_Lean_Syntax_node1(v___x_4762_, v___x_4771_, v___x_4779_);
lean_inc(v___x_4762_);
v___x_4781_ = l_Lean_Syntax_node3(v___x_4762_, v___x_4765_, v___x_4767_, v___x_4770_, v___x_4780_);
v___x_4782_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4762_);
v___x_4783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4762_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
lean_inc(v___x_4762_);
v___x_4784_ = l_Lean_Syntax_node1(v___x_4762_, v___x_4763_, v___x_4783_);
lean_inc(v___x_4762_);
v___x_4785_ = l_Lean_Syntax_node2(v___x_4762_, v___x_4764_, v___x_4781_, v___x_4784_);
v___x_4786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
lean_inc(v___x_4762_);
v___x_4788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4762_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
lean_inc(v___x_4762_);
v___x_4789_ = l_Lean_Syntax_node2(v___x_4762_, v___x_4786_, v___x_4788_, v_b_4753_);
lean_inc(v___x_4762_);
v___x_4790_ = l_Lean_Syntax_node2(v___x_4762_, v___x_4764_, v___x_4789_, v___x_4776_);
lean_inc(v___x_4762_);
v___x_4791_ = l_Lean_Syntax_node2(v___x_4762_, v___x_4763_, v___x_4785_, v___x_4790_);
v___x_4792_ = l_Lean_Syntax_node1(v___x_4762_, v___x_4759_, v___x_4791_);
v___x_4793_ = ((size_t)1ULL);
v___x_4794_ = lean_usize_add(v_i_4752_, v___x_4793_);
v_i_4752_ = v___x_4794_;
v_b_4753_ = v___x_4792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_4796_, lean_object* v_sz_4797_, lean_object* v_i_4798_, lean_object* v_b_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
size_t v_sz_boxed_4802_; size_t v_i_boxed_4803_; lean_object* v_res_4804_; 
v_sz_boxed_4802_ = lean_unbox_usize(v_sz_4797_);
lean_dec(v_sz_4797_);
v_i_boxed_4803_ = lean_unbox_usize(v_i_4798_);
lean_dec(v_i_4798_);
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4796_, v_sz_boxed_4802_, v_i_boxed_4803_, v_b_4799_, v___y_4800_);
lean_dec_ref(v___y_4800_);
lean_dec_ref(v_as_4796_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_4805_, size_t v_sz_4806_, size_t v_i_4807_, lean_object* v_b_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
uint8_t v___x_4817_; 
v___x_4817_ = lean_usize_dec_lt(v_i_4807_, v_sz_4806_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; 
v___x_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4818_, 0, v_b_4808_);
return v___x_4818_;
}
else
{
lean_object* v_ref_4819_; lean_object* v___x_4820_; lean_object* v_a_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; size_t v___x_4854_; size_t v___x_4855_; lean_object* v___x_4856_; 
v_ref_4819_ = lean_ctor_get(v___y_4814_, 5);
v___x_4820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4821_ = lean_array_uget_borrowed(v_as_4805_, v_i_4807_);
v___x_4822_ = 0;
v___x_4823_ = l_Lean_SourceInfo_fromRef(v_ref_4819_, v___x_4822_);
v___x_4824_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4826_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4823_);
v___x_4828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4823_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc(v___x_4823_);
v___x_4830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4823_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
lean_inc(v___x_4823_);
v___x_4831_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4824_, v___x_4830_);
v___x_4832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4833_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4834_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v_a_4821_);
lean_inc(v___x_4823_);
v___x_4835_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4834_, v_a_4821_);
v___x_4836_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4823_);
v___x_4837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4823_);
lean_ctor_set(v___x_4837_, 1, v___x_4824_);
lean_ctor_set(v___x_4837_, 2, v___x_4836_);
v___x_4838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
lean_inc(v___x_4823_);
v___x_4839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4823_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
lean_inc(v_a_4821_);
lean_inc_ref_n(v___x_4837_, 2);
lean_inc(v___x_4823_);
v___x_4840_ = l_Lean_Syntax_node5(v___x_4823_, v___x_4833_, v___x_4835_, v___x_4837_, v___x_4837_, v___x_4839_, v_a_4821_);
lean_inc(v___x_4823_);
v___x_4841_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4832_, v___x_4840_);
lean_inc(v___x_4823_);
v___x_4842_ = l_Lean_Syntax_node3(v___x_4823_, v___x_4826_, v___x_4828_, v___x_4831_, v___x_4841_);
v___x_4843_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
lean_inc(v___x_4823_);
v___x_4844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4823_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
lean_inc(v___x_4823_);
v___x_4845_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4824_, v___x_4844_);
lean_inc(v___x_4823_);
v___x_4846_ = l_Lean_Syntax_node2(v___x_4823_, v___x_4825_, v___x_4842_, v___x_4845_);
v___x_4847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
lean_inc(v___x_4823_);
v___x_4849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4823_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
lean_inc(v___x_4823_);
v___x_4850_ = l_Lean_Syntax_node2(v___x_4823_, v___x_4847_, v___x_4849_, v_b_4808_);
lean_inc(v___x_4823_);
v___x_4851_ = l_Lean_Syntax_node2(v___x_4823_, v___x_4825_, v___x_4850_, v___x_4837_);
lean_inc(v___x_4823_);
v___x_4852_ = l_Lean_Syntax_node2(v___x_4823_, v___x_4824_, v___x_4846_, v___x_4851_);
v___x_4853_ = l_Lean_Syntax_node1(v___x_4823_, v___x_4820_, v___x_4852_);
v___x_4854_ = ((size_t)1ULL);
v___x_4855_ = lean_usize_add(v_i_4807_, v___x_4854_);
v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4805_, v_sz_4806_, v___x_4855_, v___x_4853_, v___y_4814_);
return v___x_4856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_4857_, lean_object* v_sz_4858_, lean_object* v_i_4859_, lean_object* v_b_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
size_t v_sz_boxed_4869_; size_t v_i_boxed_4870_; lean_object* v_res_4871_; 
v_sz_boxed_4869_ = lean_unbox_usize(v_sz_4858_);
lean_dec(v_sz_4858_);
v_i_boxed_4870_ = lean_unbox_usize(v_i_4859_);
lean_dec(v_i_4859_);
v_res_4871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_4857_, v_sz_boxed_4869_, v_i_boxed_4870_, v_b_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec_ref(v_as_4857_);
return v_res_4871_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_4912_ = l_String_toRawSubstring_x27(v___x_4911_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_4927_ = l_String_toRawSubstring_x27(v___x_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_4944_, lean_object* v_dec_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v___x_4954_; uint8_t v___x_4955_; lean_object* v___y_4957_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v_body_4960_; lean_object* v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v_a_5015_; lean_object* v___y_5029_; lean_object* v___y_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v_mutTk_x3f_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; 
v___x_4954_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_4944_);
v___x_4955_ = l_Lean_Syntax_isOfKind(v_stx_4944_, v___x_4954_);
if (v___x_4955_ == 0)
{
lean_object* v___x_5117_; 
lean_dec_ref(v_dec_4945_);
lean_dec(v_stx_4944_);
v___x_5117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5117_;
}
else
{
lean_object* v___x_5118_; lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5118_ = lean_unsigned_to_nat(1u);
v___x_5119_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_5118_);
v___x_5120_ = l_Lean_Syntax_isNone(v___x_5119_);
if (v___x_5120_ == 0)
{
uint8_t v___x_5121_; 
lean_inc(v___x_5119_);
v___x_5121_ = l_Lean_Syntax_matchesNull(v___x_5119_, v___x_5118_);
if (v___x_5121_ == 0)
{
lean_object* v___x_5122_; 
lean_dec(v___x_5119_);
lean_dec_ref(v_dec_4945_);
lean_dec(v_stx_4944_);
v___x_5122_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5122_;
}
else
{
lean_object* v___x_5123_; lean_object* v_mutTk_x3f_5124_; lean_object* v___x_5125_; 
v___x_5123_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5124_ = l_Lean_Syntax_getArg(v___x_5119_, v___x_5123_);
lean_dec(v___x_5119_);
v___x_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5125_, 0, v_mutTk_x3f_5124_);
v_mutTk_x3f_5091_ = v___x_5125_;
v___y_5092_ = v_a_4946_;
v___y_5093_ = v_a_4947_;
v___y_5094_ = v_a_4948_;
v___y_5095_ = v_a_4949_;
v___y_5096_ = v_a_4950_;
v___y_5097_ = v_a_4951_;
v___y_5098_ = v_a_4952_;
goto v___jp_5090_;
}
}
else
{
lean_object* v___x_5126_; 
lean_dec(v___x_5119_);
v___x_5126_ = lean_box(0);
v_mutTk_x3f_5091_ = v___x_5126_;
v___y_5092_ = v_a_4946_;
v___y_5093_ = v_a_4947_;
v___y_5094_ = v_a_4948_;
v___y_5095_ = v_a_4949_;
v___y_5096_ = v_a_4950_;
v___y_5097_ = v_a_4951_;
v___y_5098_ = v_a_4952_;
goto v___jp_5090_;
}
}
v___jp_4956_:
{
lean_object* v_ref_4968_; uint8_t v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v_ref_4968_ = lean_ctor_get(v___y_4966_, 5);
v___x_4969_ = 0;
v___x_4970_ = l_Lean_SourceInfo_fromRef(v_ref_4968_, v___x_4969_);
v___x_4971_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_4972_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
lean_inc(v___x_4970_);
v___x_4973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4970_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4975_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_4970_);
v___x_4976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4970_);
lean_ctor_set(v___x_4976_, 1, v___x_4974_);
lean_ctor_set(v___x_4976_, 2, v___x_4975_);
v___x_4977_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref(v___x_4976_);
lean_inc(v___x_4970_);
v___x_4978_ = l_Lean_Syntax_node2(v___x_4970_, v___x_4977_, v___x_4976_, v___y_4958_);
lean_inc(v___x_4970_);
v___x_4979_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4974_, v___x_4978_);
v___x_4980_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
lean_inc(v___x_4970_);
v___x_4981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4970_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_4983_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_4984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
lean_inc(v___x_4970_);
v___x_4985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4970_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
lean_inc(v___x_4970_);
v___x_4986_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4974_, v___y_4959_);
lean_inc(v___x_4970_);
v___x_4987_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4974_, v___x_4986_);
v___x_4988_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
lean_inc(v___x_4970_);
v___x_4989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4970_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
lean_inc_ref(v___x_4989_);
lean_inc_ref(v___x_4985_);
lean_inc(v___x_4970_);
v___x_4990_ = l_Lean_Syntax_node4(v___x_4970_, v___x_4983_, v___x_4985_, v___x_4987_, v___x_4989_, v_body_4960_);
v___x_4991_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_4992_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
lean_inc(v___x_4970_);
v___x_4993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4970_);
lean_ctor_set(v___x_4993_, 1, v___x_4992_);
lean_inc(v___x_4970_);
v___x_4994_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4991_, v___x_4993_);
lean_inc(v___x_4970_);
v___x_4995_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4974_, v___x_4994_);
lean_inc(v___x_4970_);
v___x_4996_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4974_, v___x_4995_);
lean_inc(v___x_4970_);
v___x_4997_ = l_Lean_Syntax_node4(v___x_4970_, v___x_4983_, v___x_4985_, v___x_4996_, v___x_4989_, v___y_4957_);
lean_inc(v___x_4970_);
v___x_4998_ = l_Lean_Syntax_node2(v___x_4970_, v___x_4974_, v___x_4990_, v___x_4997_);
lean_inc(v___x_4970_);
v___x_4999_ = l_Lean_Syntax_node1(v___x_4970_, v___x_4982_, v___x_4998_);
lean_inc_ref_n(v___x_4976_, 2);
v___x_5000_ = l_Lean_Syntax_node7(v___x_4970_, v___x_4971_, v___x_4973_, v___x_4976_, v___x_4976_, v___x_4976_, v___x_4979_, v___x_4981_, v___x_4999_);
v___x_5001_ = l_Lean_Elab_Do_elabDoElem(v___x_5000_, v_dec_4945_, v___x_4955_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec_ref(v___y_4966_);
return v___x_5001_;
}
v___jp_5002_:
{
if (lean_obj_tag(v___y_5004_) == 0)
{
lean_dec_ref(v___y_5011_);
v___y_4957_ = v___y_5005_;
v___y_4958_ = v___y_5010_;
v___y_4959_ = v___y_5012_;
v_body_4960_ = v_a_5015_;
v___y_4961_ = v___y_5014_;
v___y_4962_ = v___y_5007_;
v___y_4963_ = v___y_5008_;
v___y_4964_ = v___y_5009_;
v___y_4965_ = v___y_5013_;
v___y_4966_ = v___y_5003_;
v___y_4967_ = v___y_5006_;
goto v___jp_4956_;
}
else
{
lean_dec_ref(v___y_5004_);
if (v___x_4955_ == 0)
{
lean_dec_ref(v___y_5011_);
v___y_4957_ = v___y_5005_;
v___y_4958_ = v___y_5010_;
v___y_4959_ = v___y_5012_;
v_body_4960_ = v_a_5015_;
v___y_4961_ = v___y_5014_;
v___y_4962_ = v___y_5007_;
v___y_4963_ = v___y_5008_;
v___y_4964_ = v___y_5009_;
v___y_4965_ = v___y_5013_;
v___y_4966_ = v___y_5003_;
v___y_4967_ = v___y_5006_;
goto v___jp_4956_;
}
else
{
size_t v_sz_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v_sz_5016_ = lean_array_size(v___y_5011_);
v___x_5017_ = ((size_t)0ULL);
v___x_5018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5011_, v_sz_5016_, v___x_5017_, v_a_5015_, v___y_5014_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5013_, v___y_5003_, v___y_5006_);
lean_dec_ref(v___y_5011_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref(v___x_5018_);
v___y_4957_ = v___y_5005_;
v___y_4958_ = v___y_5010_;
v___y_4959_ = v___y_5012_;
v_body_4960_ = v_a_5019_;
v___y_4961_ = v___y_5014_;
v___y_4962_ = v___y_5007_;
v___y_4963_ = v___y_5008_;
v___y_4964_ = v___y_5009_;
v___y_4965_ = v___y_5013_;
v___y_4966_ = v___y_5003_;
v___y_4967_ = v___y_5006_;
goto v___jp_4956_;
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v___y_5012_);
lean_dec(v___y_5010_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5003_);
lean_dec_ref(v_dec_4945_);
v_a_5020_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_5018_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5018_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
}
v___jp_5028_:
{
lean_object* v___x_5041_; 
lean_inc(v___y_5039_);
v___x_5041_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5039_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5038_, v___y_5029_, v___y_5032_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v_letOrReassign_5043_; lean_object* v___x_5044_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
lean_inc(v_a_5042_);
lean_dec_ref(v___x_5041_);
lean_inc(v___y_5030_);
v_letOrReassign_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_letOrReassign_5043_, 0, v___y_5030_);
v___x_5044_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_5043_, v_a_5042_, v___y_5037_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5038_, v___y_5029_, v___y_5032_);
lean_dec_ref(v_letOrReassign_5043_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_dec_ref(v___x_5044_);
if (lean_obj_tag(v___y_5040_) == 0)
{
lean_object* v_ref_5045_; lean_object* v_quotContext_5046_; lean_object* v_currMacroScope_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v_ref_5045_ = lean_ctor_get(v___y_5029_, 5);
v_quotContext_5046_ = lean_ctor_get(v___y_5029_, 10);
v_currMacroScope_5047_ = lean_ctor_get(v___y_5029_, 11);
v___x_5048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5049_ = 0;
v___x_5050_ = l_Lean_SourceInfo_fromRef(v_ref_5045_, v___x_5049_);
v___x_5051_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5053_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5054_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5055_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5056_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc(v_currMacroScope_5047_);
lean_inc(v_quotContext_5046_);
v___x_5057_ = l_Lean_addMacroScope(v_quotContext_5046_, v___x_5056_, v_currMacroScope_5047_);
v___x_5058_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
lean_inc(v___x_5050_);
v___x_5059_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5050_);
lean_ctor_set(v___x_5059_, 1, v___x_5055_);
lean_ctor_set(v___x_5059_, 2, v___x_5057_);
lean_ctor_set(v___x_5059_, 3, v___x_5058_);
v___x_5060_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5061_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
lean_inc(v_currMacroScope_5047_);
lean_inc(v_quotContext_5046_);
v___x_5062_ = l_Lean_addMacroScope(v_quotContext_5046_, v___x_5061_, v_currMacroScope_5047_);
v___x_5063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
lean_inc(v___x_5050_);
v___x_5064_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5050_);
lean_ctor_set(v___x_5064_, 1, v___x_5060_);
lean_ctor_set(v___x_5064_, 2, v___x_5062_);
lean_ctor_set(v___x_5064_, 3, v___x_5063_);
lean_inc(v___x_5050_);
v___x_5065_ = l_Lean_Syntax_node1(v___x_5050_, v___x_5051_, v___x_5064_);
lean_inc(v___x_5050_);
v___x_5066_ = l_Lean_Syntax_node2(v___x_5050_, v___x_5054_, v___x_5059_, v___x_5065_);
lean_inc(v___x_5050_);
v___x_5067_ = l_Lean_Syntax_node1(v___x_5050_, v___x_5053_, v___x_5066_);
v___x_5068_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc(v___x_5050_);
v___x_5069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5050_);
lean_ctor_set(v___x_5069_, 1, v___x_5051_);
lean_ctor_set(v___x_5069_, 2, v___x_5068_);
lean_inc(v___x_5050_);
v___x_5070_ = l_Lean_Syntax_node2(v___x_5050_, v___x_5052_, v___x_5067_, v___x_5069_);
lean_inc(v___x_5050_);
v___x_5071_ = l_Lean_Syntax_node1(v___x_5050_, v___x_5051_, v___x_5070_);
v___x_5072_ = l_Lean_Syntax_node1(v___x_5050_, v___x_5048_, v___x_5071_);
v___y_5003_ = v___y_5029_;
v___y_5004_ = v___y_5030_;
v___y_5005_ = v___y_5031_;
v___y_5006_ = v___y_5032_;
v___y_5007_ = v___y_5033_;
v___y_5008_ = v___y_5034_;
v___y_5009_ = v___y_5035_;
v___y_5010_ = v___y_5036_;
v___y_5011_ = v_a_5042_;
v___y_5012_ = v___y_5039_;
v___y_5013_ = v___y_5038_;
v___y_5014_ = v___y_5037_;
v_a_5015_ = v___x_5072_;
goto v___jp_5002_;
}
else
{
lean_object* v_val_5073_; 
v_val_5073_ = lean_ctor_get(v___y_5040_, 0);
lean_inc(v_val_5073_);
lean_dec_ref(v___y_5040_);
v___y_5003_ = v___y_5029_;
v___y_5004_ = v___y_5030_;
v___y_5005_ = v___y_5031_;
v___y_5006_ = v___y_5032_;
v___y_5007_ = v___y_5033_;
v___y_5008_ = v___y_5034_;
v___y_5009_ = v___y_5035_;
v___y_5010_ = v___y_5036_;
v___y_5011_ = v_a_5042_;
v___y_5012_ = v___y_5039_;
v___y_5013_ = v___y_5038_;
v___y_5014_ = v___y_5037_;
v_a_5015_ = v_val_5073_;
goto v___jp_5002_;
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_dec(v_a_5042_);
lean_dec(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec(v___y_5036_);
lean_dec(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec_ref(v_dec_4945_);
v_a_5074_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_5044_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5044_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_dec(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec(v___y_5036_);
lean_dec(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec_ref(v_dec_4945_);
v_a_5082_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5041_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5041_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
v___jp_5090_:
{
lean_object* v___x_5099_; lean_object* v_pattern_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5099_ = lean_unsigned_to_nat(2u);
v_pattern_5100_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_5099_);
v___x_5101_ = lean_unsigned_to_nat(4u);
v___x_5102_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_5101_);
v___x_5103_ = lean_unsigned_to_nat(6u);
v___x_5104_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_5103_);
v___x_5105_ = lean_unsigned_to_nat(7u);
v___x_5106_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_5105_);
lean_dec(v_stx_4944_);
v___x_5107_ = l_Lean_Syntax_getOptional_x3f(v___x_5106_);
lean_dec(v___x_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v___x_5108_; 
v___x_5108_ = lean_box(0);
lean_inc_ref(v___y_5097_);
v___y_5029_ = v___y_5097_;
v___y_5030_ = v_mutTk_x3f_5091_;
v___y_5031_ = v___x_5104_;
v___y_5032_ = v___y_5098_;
v___y_5033_ = v___y_5093_;
v___y_5034_ = v___y_5094_;
v___y_5035_ = v___y_5095_;
v___y_5036_ = v___x_5102_;
v___y_5037_ = v___y_5092_;
v___y_5038_ = v___y_5096_;
v___y_5039_ = v_pattern_5100_;
v___y_5040_ = v___x_5108_;
goto v___jp_5028_;
}
else
{
lean_object* v_val_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
v_val_5109_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5107_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_val_5109_);
lean_dec(v___x_5107_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_val_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
lean_inc_ref(v___y_5097_);
v___y_5029_ = v___y_5097_;
v___y_5030_ = v_mutTk_x3f_5091_;
v___y_5031_ = v___x_5104_;
v___y_5032_ = v___y_5098_;
v___y_5033_ = v___y_5093_;
v___y_5034_ = v___y_5094_;
v___y_5035_ = v___y_5095_;
v___y_5036_ = v___x_5102_;
v___y_5037_ = v___y_5092_;
v___y_5038_ = v___y_5096_;
v___y_5039_ = v_pattern_5100_;
v___y_5040_ = v___x_5114_;
goto v___jp_5028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5127_, lean_object* v_dec_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5127_, v_dec_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
lean_dec(v_a_5133_);
lean_dec_ref(v_a_5132_);
lean_dec(v_a_5131_);
lean_dec_ref(v_a_5130_);
lean_dec_ref(v_a_5129_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5138_, size_t v_sz_5139_, size_t v_i_5140_, lean_object* v_b_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5138_, v_sz_5139_, v_i_5140_, v_b_5141_, v___y_5147_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5151_, lean_object* v_sz_5152_, lean_object* v_i_5153_, lean_object* v_b_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
size_t v_sz_boxed_5163_; size_t v_i_boxed_5164_; lean_object* v_res_5165_; 
v_sz_boxed_5163_ = lean_unbox_usize(v_sz_5152_);
lean_dec(v_sz_5152_);
v_i_boxed_5164_ = lean_unbox_usize(v_i_5153_);
lean_dec(v_i_5153_);
v_res_5165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5151_, v_sz_boxed_5163_, v_i_boxed_5164_, v_b_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
lean_dec(v___y_5157_);
lean_dec_ref(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec_ref(v_as_5151_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5173_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5174_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5176_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5177_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5173_, v___x_5174_, v___x_5175_, v___x_5176_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5186_, lean_object* v_dec_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_){
_start:
{
lean_object* v_mutTk_x3f_5197_; lean_object* v___y_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; lean_object* v___y_5203_; lean_object* v___y_5204_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5209_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5186_);
v___x_5210_ = l_Lean_Syntax_isOfKind(v_stx_5186_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
lean_dec_ref(v_dec_5187_);
lean_dec(v_stx_5186_);
v___x_5211_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5211_;
}
else
{
lean_object* v___x_5212_; lean_object* v___x_5213_; uint8_t v___x_5214_; 
v___x_5212_ = lean_unsigned_to_nat(1u);
v___x_5213_ = l_Lean_Syntax_getArg(v_stx_5186_, v___x_5212_);
v___x_5214_ = l_Lean_Syntax_isNone(v___x_5213_);
if (v___x_5214_ == 0)
{
uint8_t v___x_5215_; 
lean_inc(v___x_5213_);
v___x_5215_ = l_Lean_Syntax_matchesNull(v___x_5213_, v___x_5212_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5216_; 
lean_dec(v___x_5213_);
lean_dec_ref(v_dec_5187_);
lean_dec(v_stx_5186_);
v___x_5216_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5216_;
}
else
{
lean_object* v___x_5217_; lean_object* v_mutTk_x3f_5218_; lean_object* v___x_5219_; 
v___x_5217_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5218_ = l_Lean_Syntax_getArg(v___x_5213_, v___x_5217_);
lean_dec(v___x_5213_);
v___x_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5219_, 0, v_mutTk_x3f_5218_);
v_mutTk_x3f_5197_ = v___x_5219_;
v___y_5198_ = v_a_5188_;
v___y_5199_ = v_a_5189_;
v___y_5200_ = v_a_5190_;
v___y_5201_ = v_a_5191_;
v___y_5202_ = v_a_5192_;
v___y_5203_ = v_a_5193_;
v___y_5204_ = v_a_5194_;
goto v___jp_5196_;
}
}
else
{
lean_object* v___x_5220_; 
lean_dec(v___x_5213_);
v___x_5220_ = lean_box(0);
v_mutTk_x3f_5197_ = v___x_5220_;
v___y_5198_ = v_a_5188_;
v___y_5199_ = v_a_5189_;
v___y_5200_ = v_a_5190_;
v___y_5201_ = v_a_5191_;
v___y_5202_ = v_a_5192_;
v___y_5203_ = v_a_5193_;
v___y_5204_ = v_a_5194_;
goto v___jp_5196_;
}
}
v___jp_5196_:
{
lean_object* v___x_5205_; lean_object* v_decl_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5205_ = lean_unsigned_to_nat(2u);
v_decl_5206_ = l_Lean_Syntax_getArg(v_stx_5186_, v___x_5205_);
lean_dec(v_stx_5186_);
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v_mutTk_x3f_5197_);
v___x_5208_ = l_Lean_Elab_Do_elabDoArrow(v___x_5207_, v_decl_5206_, v_dec_5187_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
return v___x_5208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5221_, lean_object* v_dec_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5221_, v_dec_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec_ref(v_a_5223_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5239_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5240_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5241_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5242_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5243_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5239_, v___x_5240_, v___x_5241_, v___x_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5252_, lean_object* v_dec_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v___x_5262_; uint8_t v___x_5263_; 
v___x_5262_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5252_);
v___x_5263_ = l_Lean_Syntax_isOfKind(v_stx_5252_, v___x_5262_);
if (v___x_5263_ == 0)
{
lean_object* v___x_5264_; 
lean_dec_ref(v_dec_5253_);
lean_dec(v_stx_5252_);
v___x_5264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5264_;
}
else
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; uint8_t v___x_5268_; 
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = l_Lean_Syntax_getArg(v_stx_5252_, v___x_5265_);
lean_dec(v_stx_5252_);
v___x_5267_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5266_);
v___x_5268_ = l_Lean_Syntax_isOfKind(v___x_5266_, v___x_5267_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5269_; uint8_t v___x_5270_; 
v___x_5269_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5266_);
v___x_5270_ = l_Lean_Syntax_isOfKind(v___x_5266_, v___x_5269_);
if (v___x_5270_ == 0)
{
lean_object* v___x_5271_; 
lean_dec(v___x_5266_);
lean_dec_ref(v_dec_5253_);
v___x_5271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5271_;
}
else
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = lean_box(2);
v___x_5273_ = l_Lean_Elab_Do_elabDoArrow(v___x_5272_, v___x_5266_, v_dec_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
return v___x_5273_;
}
}
else
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_box(2);
v___x_5275_ = l_Lean_Elab_Do_elabDoArrow(v___x_5274_, v___x_5266_, v_dec_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5276_, lean_object* v_dec_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5276_, v_dec_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
lean_dec_ref(v_a_5278_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5294_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5295_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5296_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5297_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5298_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5294_, v___x_5295_, v___x_5296_, v___x_5297_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5300_;
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
