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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__4;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__6;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__8;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "let body of "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "reassignment with `|` (i.e., \"else clause\") is not supported"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mut"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7_value;
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
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoLet"};
static const lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 0, 15, 120, 200, 84, 91, 220)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoHave"};
static const lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 115, 123, 116, 44, 216, 133, 101)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2_value;
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
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetElse___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__10;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value),LEAN_SCALAR_PTR_LITERAL(182, 237, 62, 79, 212, 57, 236, 253)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PUnit.unit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetElse___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__17;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__18_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__19_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__20_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__23 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__21_value),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__23_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__24 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabDoLetElse"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 42, 180, 235, 57, 50, 131, 26)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoLetArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(88, 6, 18, 178, 201, 235, 246, 214)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3_value;
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
lean_inc_n(v_macroStack_596_, 2);
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
lean_dec_ref(v___y_609_);
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
lean_inc_n(v___x_829_, 7);
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
v___x_839_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_839_, 0, v___x_829_);
lean_ctor_set(v___x_839_, 1, v___x_835_);
lean_ctor_set(v___x_839_, 2, v___x_837_);
lean_ctor_set(v___x_839_, 3, v___x_838_);
v___x_840_ = l_Lean_Syntax_node1(v___x_829_, v___x_834_, v___x_839_);
v___x_841_ = l_Lean_Syntax_node2(v___x_829_, v___x_831_, v___x_833_, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_829_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_845_ = l_Lean_Syntax_node1(v___x_829_, v___x_844_, v_val_825_);
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
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
v_quotContext_754_ = lean_ctor_get(v___y_738_, 10);
v_currMacroScope_755_ = lean_ctor_get(v___y_738_, 11);
v___x_756_ = l_Lean_SourceInfo_fromRef(v_ref_753_, v___x_729_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_758_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_756_, 11);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_756_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_756_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_756_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_767_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_768_ = lean_box(0);
lean_inc(v_currMacroScope_755_);
lean_inc(v_quotContext_754_);
v___x_769_ = l_Lean_addMacroScope(v_quotContext_754_, v___x_768_, v_currMacroScope_755_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_771_, 0, v___x_756_);
lean_ctor_set(v___x_771_, 1, v___x_767_);
lean_ctor_set(v___x_771_, 2, v___x_769_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_756_, v___x_766_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___x_756_, v___x_763_, v___x_765_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_756_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___x_756_, v___x_757_, v_a_749_);
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_756_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_Syntax_node5(v___x_756_, v___x_762_, v___x_773_, v___y_732_, v___x_775_, v___x_776_, v___x_778_);
lean_inc_ref(v___x_759_);
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
lean_dec(v_pattern_733_);
lean_dec(v___y_732_);
return v___x_748_;
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
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
lean_inc_n(v___x_897_, 7);
v___x_898_ = l_Lean_Syntax_node1(v___x_897_, v___x_868_, v_x_874_);
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_900_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_901_, 0, v___x_897_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_897_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_Syntax_node2(v___x_897_, v___x_902_, v___x_904_, v_a_891_);
v___x_906_ = l_Lean_Syntax_node1(v___x_897_, v___x_899_, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_897_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
lean_inc_ref(v___y_1132_);
v___x_1141_ = lean_apply_9(v_k_1131_, v_b_1135_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v_b_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1153_, lean_object* v_type_1154_, lean_object* v_val_1155_, lean_object* v_k_1156_, uint8_t v_nondep_1157_, uint8_t v_kind_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; 
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1167_, 0, v_k_1156_);
lean_closure_set(v___f_1167_, 1, v___y_1159_);
lean_closure_set(v___f_1167_, 2, v___y_1160_);
lean_closure_set(v___f_1167_, 3, v___y_1161_);
v___x_1168_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1153_, v_type_1154_, v_val_1155_, v___f_1167_, v_nondep_1157_, v_kind_1158_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1177_, lean_object* v_type_1178_, lean_object* v_val_1179_, lean_object* v_k_1180_, lean_object* v_nondep_1181_, lean_object* v_kind_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v_nondep_boxed_1191_; uint8_t v_kind_boxed_1192_; lean_object* v_res_1193_; 
v_nondep_boxed_1191_ = lean_unbox(v_nondep_1181_);
v_kind_boxed_1192_ = lean_unbox(v_kind_1182_);
v_res_1193_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1177_, v_type_1178_, v_val_1179_, v_k_1180_, v_nondep_boxed_1191_, v_kind_boxed_1192_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1194_, lean_object* v_name_1195_, lean_object* v_type_1196_, lean_object* v_val_1197_, lean_object* v_k_1198_, uint8_t v_nondep_1199_, uint8_t v_kind_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1195_, v_type_1196_, v_val_1197_, v_k_1198_, v_nondep_1199_, v_kind_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_name_1211_, lean_object* v_type_1212_, lean_object* v_val_1213_, lean_object* v_k_1214_, lean_object* v_nondep_1215_, lean_object* v_kind_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
uint8_t v_nondep_boxed_1225_; uint8_t v_kind_boxed_1226_; lean_object* v_res_1227_; 
v_nondep_boxed_1225_ = lean_unbox(v_nondep_1215_);
v_kind_boxed_1226_ = lean_unbox(v_kind_1216_);
v_res_1227_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1210_, v_name_1211_, v_type_1212_, v_val_1213_, v_k_1214_, v_nondep_boxed_1225_, v_kind_boxed_1226_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1228_, lean_object* v___x_1229_, uint8_t v___x_1230_, lean_object* v___x_1231_, lean_object* v___x_1232_, uint8_t v___x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1228_, v___x_1229_, v___x_1230_, v___x_1230_, v___x_1231_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = 1;
v___x_1244_ = l_Lean_Meta_mkLambdaFVars(v___x_1232_, v_a_1242_, v___x_1233_, v___x_1233_, v___x_1233_, v___x_1230_, v___x_1243_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1244_;
}
else
{
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v___x_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___x_76573__boxed_1258_; uint8_t v___x_76576__boxed_1259_; lean_object* v_res_1260_; 
v___x_76573__boxed_1258_ = lean_unbox(v___x_1247_);
v___x_76576__boxed_1259_ = lean_unbox(v___x_1250_);
v_res_1260_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1245_, v___x_1246_, v___x_76573__boxed_1258_, v___x_1248_, v___x_1249_, v___x_76576__boxed_1259_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___x_1249_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v_ks_1265_; lean_object* v_vs_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1290_; 
v_ks_1265_ = lean_ctor_get(v_x_1261_, 0);
v_vs_1266_ = lean_ctor_get(v_x_1261_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_x_1261_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1268_ = v_x_1261_;
v_isShared_1269_ = v_isSharedCheck_1290_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_vs_1266_);
lean_inc(v_ks_1265_);
lean_dec(v_x_1261_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1290_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_array_get_size(v_ks_1265_);
v___x_1271_ = lean_nat_dec_lt(v_x_1262_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec(v_x_1262_);
v___x_1272_ = lean_array_push(v_ks_1265_, v_x_1263_);
v___x_1273_ = lean_array_push(v_vs_1266_, v_x_1264_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1273_);
lean_ctor_set(v___x_1268_, 0, v___x_1272_);
v___x_1275_ = v___x_1268_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v_k_x27_1277_; uint8_t v___x_1278_; 
v_k_x27_1277_ = lean_array_fget_borrowed(v_ks_1265_, v_x_1262_);
v___x_1278_ = l_Lean_instBEqFVarId_beq(v_x_1263_, v_k_x27_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1280_; 
if (v_isShared_1269_ == 0)
{
v___x_1280_ = v___x_1268_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ks_1265_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_vs_1266_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_x_1262_, v___x_1281_);
lean_dec(v_x_1262_);
v_x_1261_ = v___x_1280_;
v_x_1262_ = v___x_1282_;
goto _start;
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = lean_array_fset(v_ks_1265_, v_x_1262_, v_x_1263_);
v___x_1286_ = lean_array_fset(v_vs_1266_, v_x_1262_, v_x_1264_);
lean_dec(v_x_1262_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1286_);
lean_ctor_set(v___x_1268_, 0, v___x_1285_);
v___x_1288_ = v___x_1268_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1291_, lean_object* v_k_1292_, lean_object* v_v_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1291_, v___x_1294_, v_k_1292_, v_v_1293_);
return v___x_1295_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; 
v___x_1296_ = ((size_t)5ULL);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_shift_left(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1301_ = lean_usize_sub(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1303_, size_t v_x_1304_, size_t v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
lean_object* v_es_1308_; size_t v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; lean_object* v_j_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_es_1308_ = lean_ctor_get(v_x_1303_, 0);
v___x_1309_ = ((size_t)5ULL);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_1312_ = lean_usize_land(v_x_1304_, v___x_1311_);
v_j_1313_ = lean_usize_to_nat(v___x_1312_);
v___x_1314_ = lean_array_get_size(v_es_1308_);
v___x_1315_ = lean_nat_dec_lt(v_j_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v_j_1313_);
lean_dec(v_x_1307_);
lean_dec(v_x_1306_);
return v_x_1303_;
}
else
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1352_; 
lean_inc_ref(v_es_1308_);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_x_1303_, 0);
lean_dec(v_unused_1353_);
v___x_1317_ = v_x_1303_;
v_isShared_1318_ = v_isSharedCheck_1352_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v_x_1303_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1352_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_v_1319_; lean_object* v___x_1320_; lean_object* v_xs_x27_1321_; lean_object* v___y_1323_; 
v_v_1319_ = lean_array_fget(v_es_1308_, v_j_1313_);
v___x_1320_ = lean_box(0);
v_xs_x27_1321_ = lean_array_fset(v_es_1308_, v_j_1313_, v___x_1320_);
switch(lean_obj_tag(v_v_1319_))
{
case 0:
{
lean_object* v_key_1328_; lean_object* v_val_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1339_; 
v_key_1328_ = lean_ctor_get(v_v_1319_, 0);
v_val_1329_ = lean_ctor_get(v_v_1319_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_v_1319_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1331_ = v_v_1319_;
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_val_1329_);
lean_inc(v_key_1328_);
lean_dec(v_v_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_instBEqFVarId_beq(v_x_1306_, v_key_1328_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1331_);
v___x_1334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1328_, v_val_1329_, v_x_1306_, v_x_1307_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___y_1323_ = v___x_1335_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_val_1329_);
lean_dec(v_key_1328_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v_x_1307_);
lean_ctor_set(v___x_1331_, 0, v_x_1306_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_x_1306_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_x_1307_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v___y_1323_ = v___x_1337_;
goto v___jp_1322_;
}
}
}
}
case 1:
{
lean_object* v_node_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1350_; 
v_node_1340_ = lean_ctor_get(v_v_1319_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_v_1319_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1342_ = v_v_1319_;
v_isShared_1343_ = v_isSharedCheck_1350_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_node_1340_);
lean_dec(v_v_1319_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1350_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1344_ = lean_usize_shift_right(v_x_1304_, v___x_1309_);
v___x_1345_ = lean_usize_add(v_x_1305_, v___x_1310_);
v___x_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1340_, v___x_1344_, v___x_1345_, v_x_1306_, v_x_1307_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v___y_1323_ = v___x_1348_;
goto v___jp_1322_;
}
}
}
default: 
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_x_1306_);
lean_ctor_set(v___x_1351_, 1, v_x_1307_);
v___y_1323_ = v___x_1351_;
goto v___jp_1322_;
}
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_array_fset(v_xs_x27_1321_, v_j_1313_, v___y_1323_);
lean_dec(v_j_1313_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1324_);
v___x_1326_ = v___x_1317_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
else
{
lean_object* v_ks_1354_; lean_object* v_vs_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1375_; 
v_ks_1354_ = lean_ctor_get(v_x_1303_, 0);
v_vs_1355_ = lean_ctor_get(v_x_1303_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1357_ = v_x_1303_;
v_isShared_1358_ = v_isSharedCheck_1375_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_vs_1355_);
lean_inc(v_ks_1354_);
lean_dec(v_x_1303_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1375_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1355_);
v___x_1360_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v_newNode_1361_; uint8_t v___y_1363_; size_t v___x_1369_; uint8_t v___x_1370_; 
v_newNode_1361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1360_, v_x_1306_, v_x_1307_);
v___x_1369_ = ((size_t)7ULL);
v___x_1370_ = lean_usize_dec_le(v___x_1369_, v_x_1305_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1371_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1361_);
v___x_1372_ = lean_unsigned_to_nat(4u);
v___x_1373_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
lean_dec(v___x_1371_);
v___y_1363_ = v___x_1373_;
goto v___jp_1362_;
}
else
{
v___y_1363_ = v___x_1370_;
goto v___jp_1362_;
}
v___jp_1362_:
{
if (v___y_1363_ == 0)
{
lean_object* v_ks_1364_; lean_object* v_vs_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_ks_1364_ = lean_ctor_get(v_newNode_1361_, 0);
lean_inc_ref(v_ks_1364_);
v_vs_1365_ = lean_ctor_get(v_newNode_1361_, 1);
lean_inc_ref(v_vs_1365_);
lean_dec_ref(v_newNode_1361_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2);
v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1305_, v_ks_1364_, v_vs_1365_, v___x_1366_, v___x_1367_);
lean_dec_ref(v_vs_1365_);
lean_dec_ref(v_ks_1364_);
return v___x_1368_;
}
else
{
return v_newNode_1361_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1376_, lean_object* v_keys_1377_, lean_object* v_vals_1378_, lean_object* v_i_1379_, lean_object* v_entries_1380_){
_start:
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = lean_array_get_size(v_keys_1377_);
v___x_1382_ = lean_nat_dec_lt(v_i_1379_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec(v_i_1379_);
return v_entries_1380_;
}
else
{
lean_object* v_k_1383_; lean_object* v_v_1384_; uint64_t v___x_1385_; size_t v_h_1386_; size_t v___x_1387_; lean_object* v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; size_t v_h_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_k_1383_ = lean_array_fget_borrowed(v_keys_1377_, v_i_1379_);
v_v_1384_ = lean_array_fget_borrowed(v_vals_1378_, v_i_1379_);
v___x_1385_ = l_Lean_instHashableFVarId_hash(v_k_1383_);
v_h_1386_ = lean_uint64_to_usize(v___x_1385_);
v___x_1387_ = ((size_t)5ULL);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = ((size_t)1ULL);
v___x_1390_ = lean_usize_sub(v_depth_1376_, v___x_1389_);
v___x_1391_ = lean_usize_mul(v___x_1387_, v___x_1390_);
v_h_1392_ = lean_usize_shift_right(v_h_1386_, v___x_1391_);
v___x_1393_ = lean_nat_add(v_i_1379_, v___x_1388_);
lean_dec(v_i_1379_);
lean_inc(v_v_1384_);
lean_inc(v_k_1383_);
v___x_1394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1380_, v_h_1392_, v_depth_1376_, v_k_1383_, v_v_1384_);
v_i_1379_ = v___x_1393_;
v_entries_1380_ = v___x_1394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1396_, lean_object* v_keys_1397_, lean_object* v_vals_1398_, lean_object* v_i_1399_, lean_object* v_entries_1400_){
_start:
{
size_t v_depth_boxed_1401_; lean_object* v_res_1402_; 
v_depth_boxed_1401_ = lean_unbox_usize(v_depth_1396_);
lean_dec(v_depth_1396_);
v_res_1402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1401_, v_keys_1397_, v_vals_1398_, v_i_1399_, v_entries_1400_);
lean_dec_ref(v_vals_1398_);
lean_dec_ref(v_keys_1397_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
size_t v_x_76708__boxed_1408_; size_t v_x_76709__boxed_1409_; lean_object* v_res_1410_; 
v_x_76708__boxed_1408_ = lean_unbox_usize(v_x_1404_);
lean_dec(v_x_1404_);
v_x_76709__boxed_1409_ = lean_unbox_usize(v_x_1405_);
lean_dec(v_x_1405_);
v_res_1410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1403_, v_x_76708__boxed_1408_, v_x_76709__boxed_1409_, v_x_1406_, v_x_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
uint64_t v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = l_Lean_instHashableFVarId_hash(v_x_1412_);
v___x_1415_ = lean_uint64_to_usize(v___x_1414_);
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1411_, v___x_1415_, v___x_1416_, v_x_1412_, v_x_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1418_, size_t v_i_1419_, size_t v_stop_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v___y_1423_; uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_eq(v_i_1419_, v_stop_1420_);
if (v___x_1427_ == 0)
{
lean_object* v_fvarIdToDecl_1428_; lean_object* v_decls_1429_; lean_object* v_auxDeclToFullName_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_fvarIdToDecl_1428_ = lean_ctor_get(v_b_1421_, 0);
v_decls_1429_ = lean_ctor_get(v_b_1421_, 1);
v_auxDeclToFullName_1430_ = lean_ctor_get(v_b_1421_, 2);
v___x_1431_ = lean_array_uget_borrowed(v_as_1418_, v_i_1419_);
v___x_1432_ = l_Lean_Expr_fvarId_x21(v___x_1431_);
lean_inc_ref(v_b_1421_);
v___x_1433_ = lean_local_ctx_find(v_b_1421_, v___x_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
v___y_1423_ = v_b_1421_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1460_; 
lean_inc(v_auxDeclToFullName_1430_);
lean_inc_ref(v_decls_1429_);
lean_inc_ref(v_fvarIdToDecl_1428_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_b_1421_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1461_ = lean_ctor_get(v_b_1421_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_b_1421_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_b_1421_, 0);
lean_dec(v_unused_1463_);
v___x_1435_ = v_b_1421_;
v_isShared_1436_ = v_isSharedCheck_1460_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v_b_1421_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1460_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_val_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1459_; 
v_val_1437_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1439_ = v___x_1433_;
v_isShared_1440_ = v_isSharedCheck_1459_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_val_1437_);
lean_dec(v___x_1433_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1459_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1455_; lean_object* v_fvarId_1458_; 
v___x_1441_ = l_Lean_LocalDecl_type(v_val_1437_);
v___x_1442_ = l_Lean_Expr_cleanupAnnotations(v___x_1441_);
v___x_1443_ = l_Lean_LocalDecl_setType(v_val_1437_, v___x_1442_);
v_fvarId_1458_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_fvarId_1458_);
v___y_1455_ = v_fvarId_1458_;
goto v___jp_1454_;
v___jp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1443_);
v___x_1448_ = v___x_1439_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1443_);
v___x_1448_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = l_Lean_PersistentArray_set___redArg(v_decls_1429_, v___y_1446_, v___x_1448_);
lean_dec(v___y_1446_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1449_);
lean_ctor_set(v___x_1435_, 0, v___y_1445_);
v___x_1451_ = v___x_1435_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___y_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_auxDeclToFullName_1430_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
v___y_1423_ = v___x_1451_;
goto v___jp_1422_;
}
}
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v_index_1457_; 
lean_inc_ref(v___x_1443_);
v___x_1456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1428_, v___y_1455_, v___x_1443_);
v_index_1457_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_index_1457_);
v___y_1445_ = v___x_1456_;
v___y_1446_ = v_index_1457_;
goto v___jp_1444_;
}
}
}
}
}
else
{
return v_b_1421_;
}
v___jp_1422_:
{
size_t v___x_1424_; size_t v___x_1425_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1419_, v___x_1424_);
v_i_1419_ = v___x_1425_;
v_b_1421_ = v___y_1423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1464_, lean_object* v_i_1465_, lean_object* v_stop_1466_, lean_object* v_b_1467_){
_start:
{
size_t v_i_boxed_1468_; size_t v_stop_boxed_1469_; lean_object* v_res_1470_; 
v_i_boxed_1468_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_stop_boxed_1469_ = lean_unbox_usize(v_stop_1466_);
lean_dec(v_stop_1466_);
v_res_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1464_, v_i_boxed_1468_, v_stop_boxed_1469_, v_b_1467_);
lean_dec_ref(v_as_1464_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_bs_1473_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1474_ == 0)
{
return v_bs_1473_;
}
else
{
lean_object* v_v_1475_; lean_object* v_snd_1476_; lean_object* v___x_1477_; lean_object* v_bs_x27_1478_; size_t v___x_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v_v_1475_ = lean_array_uget_borrowed(v_bs_1473_, v_i_1472_);
v_snd_1476_ = lean_ctor_get(v_v_1475_, 1);
lean_inc(v_snd_1476_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v_bs_x27_1478_ = lean_array_uset(v_bs_1473_, v_i_1472_, v___x_1477_);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1472_, v___x_1479_);
v___x_1481_ = lean_array_uset(v_bs_x27_1478_, v_i_1472_, v_snd_1476_);
v_i_1472_ = v___x_1480_;
v_bs_1473_ = v___x_1481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1483_, lean_object* v_i_1484_, lean_object* v_bs_1485_){
_start:
{
size_t v_sz_boxed_1486_; size_t v_i_boxed_1487_; lean_object* v_res_1488_; 
v_sz_boxed_1486_ = lean_unbox_usize(v_sz_1483_);
lean_dec(v_sz_1483_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1486_, v_i_boxed_1487_, v_bs_1485_);
return v_res_1488_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1500_, lean_object* v_value_1501_, uint8_t v___x_1502_, uint8_t v___x_1503_, lean_object* v___x_1504_, uint8_t v___y_1505_, lean_object* v_xs_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
lean_inc(v_type_1500_);
v___x_1514_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1514_, 0, v_type_1500_);
v___x_1515_ = 2;
v___x_1516_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1514_, v___x_1515_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; size_t v_sz_1518_; size_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___y_1522_; lean_object* v___y_1558_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v_sz_1518_ = lean_array_size(v_xs_1506_);
v___x_1519_ = ((size_t)0ULL);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1518_, v___x_1519_, v_xs_1506_);
if (v___y_1505_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1558_ = v___x_1594_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1558_ = v___x_1595_;
goto v___jp_1557_;
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
lean_inc(v_a_1517_);
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_a_1517_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_box(v___x_1502_);
v___x_1526_ = lean_box(v___x_1503_);
lean_inc_ref(v___x_1520_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1527_, 0, v_value_1501_);
lean_closure_set(v___f_1527_, 1, v___x_1523_);
lean_closure_set(v___f_1527_, 2, v___x_1525_);
lean_closure_set(v___f_1527_, 3, v___x_1524_);
lean_closure_set(v___f_1527_, 4, v___x_1520_);
lean_closure_set(v___f_1527_, 5, v___x_1526_);
v___x_1528_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1522_, v___f_1527_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = 1;
v___x_1531_ = l_Lean_Meta_mkForallFVars(v___x_1520_, v_a_1517_, v___x_1503_, v___x_1502_, v___x_1502_, v___x_1530_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec_ref(v___x_1520_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1540_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1540_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1540_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_a_1532_);
lean_ctor_set(v___x_1536_, 1, v_a_1529_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1536_);
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1529_);
v_a_1541_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1531_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1531_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v___x_1520_);
lean_dec(v_a_1517_);
v_a_1549_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1528_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1528_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
v___jp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1558_);
v___x_1560_ = l_Lean_stringToMessageData(v___y_1558_);
lean_inc_ref(v___x_1560_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_inc(v_type_1500_);
v___x_1564_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1517_, v_type_1500_, v___x_1563_, v___y_1508_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec_ref(v___x_1564_);
v___x_1565_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1560_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___x_1562_);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_inc(v_a_1517_);
v___x_1569_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1517_, v_type_1500_, v___x_1568_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_lctx_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
lean_dec_ref(v___x_1569_);
v_lctx_1570_ = lean_ctor_get(v___y_1509_, 2);
v___x_1571_ = lean_array_get_size(v___x_1520_);
v___x_1572_ = lean_nat_dec_lt(v___x_1504_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_inc_ref(v_lctx_1570_);
v___y_1522_ = v_lctx_1570_;
goto v___jp_1521_;
}
else
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_le(v___x_1571_, v___x_1571_);
if (v___x_1573_ == 0)
{
if (v___x_1572_ == 0)
{
lean_inc_ref(v_lctx_1570_);
v___y_1522_ = v_lctx_1570_;
goto v___jp_1521_;
}
else
{
size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_usize_of_nat(v___x_1571_);
lean_inc_ref(v_lctx_1570_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1520_, v___x_1519_, v___x_1574_, v_lctx_1570_);
v___y_1522_ = v___x_1575_;
goto v___jp_1521_;
}
}
else
{
size_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_usize_of_nat(v___x_1571_);
lean_inc_ref(v_lctx_1570_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1520_, v___x_1519_, v___x_1576_, v_lctx_1570_);
v___y_1522_ = v___x_1577_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1520_);
lean_dec(v_a_1517_);
lean_dec(v_value_1501_);
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___x_1560_);
lean_dec_ref(v___x_1520_);
lean_dec(v_a_1517_);
lean_dec(v_value_1501_);
lean_dec(v_type_1500_);
v_a_1586_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1564_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1564_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_xs_1506_);
lean_dec(v_value_1501_);
lean_dec(v_type_1500_);
v_a_1596_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1516_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1516_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1604_, lean_object* v_value_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___y_1609_, lean_object* v_xs_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_77027__boxed_1618_; uint8_t v___x_77028__boxed_1619_; uint8_t v___y_77030__boxed_1620_; lean_object* v_res_1621_; 
v___x_77027__boxed_1618_ = lean_unbox(v___x_1606_);
v___x_77028__boxed_1619_ = lean_unbox(v___x_1607_);
v___y_77030__boxed_1620_ = lean_unbox(v___y_1609_);
v_res_1621_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1604_, v_value_1605_, v___x_77027__boxed_1618_, v___x_77028__boxed_1619_, v___x_1608_, v___y_77030__boxed_1620_, v_xs_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___x_1608_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_dec_1622_, lean_object* v_x_1623_, uint8_t v___x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_1622_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_array_push(v___x_1636_, v_x_1623_);
v___x_1638_ = 1;
v___x_1639_ = l_Lean_Meta_mkLetFVars(v___x_1637_, v_a_1634_, v___x_1624_, v___x_1624_, v___x_1638_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec_ref(v___x_1637_);
return v___x_1639_;
}
else
{
lean_dec_ref(v_x_1623_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object* v_dec_1640_, lean_object* v_x_1641_, lean_object* v___x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
uint8_t v___x_77252__boxed_1651_; lean_object* v_res_1652_; 
v___x_77252__boxed_1651_ = lean_unbox(v___x_1642_);
v_res_1652_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_dec_1640_, v_x_1641_, v___x_77252__boxed_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_1653_, lean_object* v_dec_1654_, uint8_t v___x_1655_, lean_object* v_letOrReassign_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
lean_inc_ref(v_x_1658_);
v___x_1667_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1653_, v_x_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v___x_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v___x_1667_);
v___x_1668_ = lean_box(v___x_1655_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 11, 3);
lean_closure_set(v___f_1669_, 0, v_dec_1654_);
lean_closure_set(v___f_1669_, 1, v_x_1658_);
lean_closure_set(v___f_1669_, 2, v___x_1668_);
v___x_1670_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1656_, v_a_1657_, v___f_1669_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1670_;
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_letOrReassign_1656_);
lean_dec_ref(v_dec_1654_);
v_a_1671_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1667_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object* v_id_1679_, lean_object* v_dec_1680_, lean_object* v___x_1681_, lean_object* v_letOrReassign_1682_, lean_object* v_a_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_77294__boxed_1693_; lean_object* v_res_1694_; 
v___x_77294__boxed_1693_ = lean_unbox(v___x_1681_);
v_res_1694_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_1679_, v_dec_1680_, v___x_77294__boxed_1693_, v_letOrReassign_1682_, v_a_1683_, v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v___x_1695_, lean_object* v___x_1696_, uint8_t v___x_1697_, lean_object* v___x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_1695_, v___x_1696_, v___x_1697_, v___x_1697_, v___x_1698_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_1708_, lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v___x_77351__boxed_1720_; lean_object* v_res_1721_; 
v___x_77351__boxed_1720_ = lean_unbox(v___x_1710_);
v_res_1721_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_1708_, v___x_1709_, v___x_77351__boxed_1720_, v___x_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
lean_inc_ref(v___y_1723_);
v___x_1731_ = lean_apply_8(v_x_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, lean_box(0));
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v___y_1733_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1742_, lean_object* v_mkInfoTree_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v_a_1749_, lean_object* v_a_x3f_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v_infoState_1753_; lean_object* v_trees_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_st_ref_get(v___y_1742_);
v_infoState_1753_ = lean_ctor_get(v___x_1752_, 7);
lean_inc_ref(v_infoState_1753_);
lean_dec(v___x_1752_);
v_trees_1754_ = lean_ctor_get(v_infoState_1753_, 2);
lean_inc_ref(v_trees_1754_);
lean_dec_ref(v_infoState_1753_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1744_);
v___x_1755_ = lean_apply_8(v_mkInfoTree_1743_, v_trees_1754_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1742_, lean_box(0));
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1794_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1794_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1794_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v_infoState_1761_; lean_object* v_env_1762_; lean_object* v_nextMacroScope_1763_; lean_object* v_ngen_1764_; lean_object* v_auxDeclNGen_1765_; lean_object* v_traceState_1766_; lean_object* v_cache_1767_; lean_object* v_messages_1768_; lean_object* v_snapshotTasks_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1793_; 
v___x_1760_ = lean_st_ref_take(v___y_1742_);
v_infoState_1761_ = lean_ctor_get(v___x_1760_, 7);
v_env_1762_ = lean_ctor_get(v___x_1760_, 0);
v_nextMacroScope_1763_ = lean_ctor_get(v___x_1760_, 1);
v_ngen_1764_ = lean_ctor_get(v___x_1760_, 2);
v_auxDeclNGen_1765_ = lean_ctor_get(v___x_1760_, 3);
v_traceState_1766_ = lean_ctor_get(v___x_1760_, 4);
v_cache_1767_ = lean_ctor_get(v___x_1760_, 5);
v_messages_1768_ = lean_ctor_get(v___x_1760_, 6);
v_snapshotTasks_1769_ = lean_ctor_get(v___x_1760_, 8);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snapshotTasks_1769_);
lean_inc(v_infoState_1761_);
lean_inc(v_messages_1768_);
lean_inc(v_cache_1767_);
lean_inc(v_traceState_1766_);
lean_inc(v_auxDeclNGen_1765_);
lean_inc(v_ngen_1764_);
lean_inc(v_nextMacroScope_1763_);
lean_inc(v_env_1762_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1793_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint8_t v_enabled_1773_; lean_object* v_assignment_1774_; lean_object* v_lazyAssignment_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1791_; 
v_enabled_1773_ = lean_ctor_get_uint8(v_infoState_1761_, sizeof(void*)*3);
v_assignment_1774_ = lean_ctor_get(v_infoState_1761_, 0);
v_lazyAssignment_1775_ = lean_ctor_get(v_infoState_1761_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_infoState_1761_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_infoState_1761_, 2);
lean_dec(v_unused_1792_);
v___x_1777_ = v_infoState_1761_;
v_isShared_1778_ = v_isSharedCheck_1791_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_lazyAssignment_1775_);
lean_inc(v_assignment_1774_);
lean_dec(v_infoState_1761_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1791_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_PersistentArray_push___redArg(v_a_1749_, v_a_1756_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 2, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_assignment_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_lazyAssignment_1775_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v___x_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*3, v_enabled_1773_);
v___x_1781_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 7, v___x_1781_);
v___x_1783_ = v___x_1771_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_env_1762_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_nextMacroScope_1763_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_ngen_1764_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_auxDeclNGen_1765_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_traceState_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_cache_1767_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_messages_1768_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_snapshotTasks_1769_);
v___x_1783_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_st_ref_set(v___y_1742_, v___x_1783_);
v___x_1785_ = lean_box(0);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1785_);
v___x_1787_ = v___x_1758_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_a_1749_);
v_a_1795_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1755_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1755_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_1803_, lean_object* v_mkInfoTree_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v_a_1810_, lean_object* v_a_x3f_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1803_, v_mkInfoTree_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v_a_1810_, v_a_x3f_1811_);
lean_dec(v_a_x3f_1811_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1803_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_infoState_1817_; lean_object* v_trees_1818_; lean_object* v___x_1819_; lean_object* v_infoState_1820_; lean_object* v_env_1821_; lean_object* v_nextMacroScope_1822_; lean_object* v_ngen_1823_; lean_object* v_auxDeclNGen_1824_; lean_object* v_traceState_1825_; lean_object* v_cache_1826_; lean_object* v_messages_1827_; lean_object* v_snapshotTasks_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1851_; 
v___x_1816_ = lean_st_ref_get(v___y_1814_);
v_infoState_1817_ = lean_ctor_get(v___x_1816_, 7);
lean_inc_ref(v_infoState_1817_);
lean_dec(v___x_1816_);
v_trees_1818_ = lean_ctor_get(v_infoState_1817_, 2);
lean_inc_ref(v_trees_1818_);
lean_dec_ref(v_infoState_1817_);
v___x_1819_ = lean_st_ref_take(v___y_1814_);
v_infoState_1820_ = lean_ctor_get(v___x_1819_, 7);
v_env_1821_ = lean_ctor_get(v___x_1819_, 0);
v_nextMacroScope_1822_ = lean_ctor_get(v___x_1819_, 1);
v_ngen_1823_ = lean_ctor_get(v___x_1819_, 2);
v_auxDeclNGen_1824_ = lean_ctor_get(v___x_1819_, 3);
v_traceState_1825_ = lean_ctor_get(v___x_1819_, 4);
v_cache_1826_ = lean_ctor_get(v___x_1819_, 5);
v_messages_1827_ = lean_ctor_get(v___x_1819_, 6);
v_snapshotTasks_1828_ = lean_ctor_get(v___x_1819_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1851_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snapshotTasks_1828_);
lean_inc(v_infoState_1820_);
lean_inc(v_messages_1827_);
lean_inc(v_cache_1826_);
lean_inc(v_traceState_1825_);
lean_inc(v_auxDeclNGen_1824_);
lean_inc(v_ngen_1823_);
lean_inc(v_nextMacroScope_1822_);
lean_inc(v_env_1821_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1851_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
uint8_t v_enabled_1832_; lean_object* v_assignment_1833_; lean_object* v_lazyAssignment_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1849_; 
v_enabled_1832_ = lean_ctor_get_uint8(v_infoState_1820_, sizeof(void*)*3);
v_assignment_1833_ = lean_ctor_get(v_infoState_1820_, 0);
v_lazyAssignment_1834_ = lean_ctor_get(v_infoState_1820_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_infoState_1820_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_infoState_1820_, 2);
lean_dec(v_unused_1850_);
v___x_1836_ = v_infoState_1820_;
v_isShared_1837_ = v_isSharedCheck_1849_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_lazyAssignment_1834_);
lean_inc(v_assignment_1833_);
lean_dec(v_infoState_1820_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1849_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1838_ = lean_unsigned_to_nat(32u);
v___x_1839_ = lean_mk_empty_array_with_capacity(v___x_1838_);
lean_dec_ref(v___x_1839_);
v___x_1840_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 2, v___x_1840_);
v___x_1842_ = v___x_1836_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_assignment_1833_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_lazyAssignment_1834_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v___x_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1848_, sizeof(void*)*3, v_enabled_1832_);
v___x_1842_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 7, v___x_1842_);
v___x_1844_ = v___x_1830_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_env_1821_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_nextMacroScope_1822_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_ngen_1823_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_auxDeclNGen_1824_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_traceState_1825_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_messages_1827_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_snapshotTasks_1828_);
v___x_1844_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_st_ref_set(v___y_1814_, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_trees_1818_);
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1852_);
lean_dec(v___y_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_1855_, lean_object* v_mkInfoTree_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v_infoState_1865_; uint8_t v_enabled_1866_; 
v___x_1864_ = lean_st_ref_get(v___y_1862_);
v_infoState_1865_ = lean_ctor_get(v___x_1864_, 7);
lean_inc_ref(v_infoState_1865_);
lean_dec(v___x_1864_);
v_enabled_1866_ = lean_ctor_get_uint8(v_infoState_1865_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1865_);
if (v_enabled_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref(v_mkInfoTree_1856_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc_ref(v___y_1859_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v___x_1867_ = lean_apply_7(v_x_1855_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, lean_box(0));
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v_r_1870_; 
v___x_1868_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1862_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc_ref(v___y_1859_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
v_r_1870_ = lean_apply_7(v_x_1855_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, lean_box(0));
if (lean_obj_tag(v_r_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1895_; 
v_a_1871_ = lean_ctor_get(v_r_1870_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_r_1870_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1873_ = v_r_1870_;
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v_r_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1895_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
lean_inc(v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1862_, v_mkInfoTree_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v_a_1869_, v___x_1876_);
lean_dec_ref(v___x_1876_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1885_);
v___x_1879_ = v___x_1877_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_dec(v___x_1877_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_a_1871_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1871_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1871_);
v_a_1886_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1877_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1877_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v_r_1870_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v_r_1870_);
v___x_1897_ = lean_box(0);
v___x_1898_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1862_, v_mkInfoTree_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v_a_1869_, v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___x_1898_, 0);
lean_dec(v_unused_1906_);
v___x_1900_ = v___x_1898_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v___x_1898_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 1);
lean_ctor_set(v___x_1900_, 0, v_a_1896_);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1896_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1896_);
v_a_1907_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1898_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1898_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_1915_, lean_object* v_mkInfoTree_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_1915_, v_mkInfoTree_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_1925_, lean_object* v_output_1926_, lean_object* v_trees_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_lctx_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_lctx_1935_ = lean_ctor_get(v___y_1930_, 2);
lean_inc_ref(v_lctx_1935_);
v___x_1936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1936_, 0, v_lctx_1935_);
lean_ctor_set(v___x_1936_, 1, v_stx_1925_);
lean_ctor_set(v___x_1936_, 2, v_output_1926_);
v___x_1937_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v_trees_1927_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_1940_, lean_object* v_output_1941_, lean_object* v_trees_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_1940_, v_output_1941_, v_trees_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_1951_, lean_object* v_output_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___f_1961_; lean_object* v___x_1962_; 
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1961_, 0, v_stx_1951_);
lean_closure_set(v___f_1961_, 1, v_output_1952_);
v___x_1962_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_1953_, v___f_1961_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_1963_, lean_object* v_output_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_1963_, v_output_1964_, v_x_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_1974_, lean_object* v_afterStx_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_inc_ref(v___y_1977_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1985_, 0, v_x_1976_);
lean_closure_set(v___f_1985_, 1, v___y_1977_);
lean_inc(v_afterStx_1975_);
lean_inc(v_beforeStx_1974_);
v___x_1986_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_1986_, 0, lean_box(0));
lean_closure_set(v___x_1986_, 1, v_beforeStx_1974_);
lean_closure_set(v___x_1986_, 2, v_afterStx_1975_);
lean_closure_set(v___x_1986_, 3, v___f_1985_);
v___x_1987_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_1974_, v_afterStx_1975_, v___x_1986_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1987_) == 0)
{
return v___x_1987_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_1996_, lean_object* v_afterStx_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_1996_, v_afterStx_1997_, v_x_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__1));
v___x_2011_ = l_String_toRawSubstring_x27(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_a_2033_, lean_object* v_rhs_2034_, uint8_t v___x_2035_, lean_object* v___x_2036_, lean_object* v___x_2037_, lean_object* v___x_2038_, lean_object* v___x_2039_, uint8_t v___x_2040_, lean_object* v_body_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_ref_2050_; lean_object* v_quotContext_2051_; lean_object* v_currMacroScope_2052_; lean_object* v___x_2053_; 
v_ref_2050_ = lean_ctor_get(v___y_2047_, 5);
v_quotContext_2051_ = lean_ctor_get(v___y_2047_, 10);
v_currMacroScope_2052_ = lean_ctor_get(v___y_2047_, 11);
lean_inc_ref(v_a_2033_);
v___x_2053_ = l_Lean_Elab_Term_exprToSyntax(v_a_2033_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v_ref_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v_ref_2055_ = l_Lean_replaceRef(v_rhs_2034_, v_ref_2050_);
v___x_2056_ = l_Lean_SourceInfo_fromRef(v_ref_2055_, v___x_2035_);
lean_dec(v_ref_2055_);
v___x_2057_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__0));
lean_inc_n(v___x_2056_, 2);
v___x_2058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__2);
v___x_2060_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__3));
lean_inc(v_currMacroScope_2052_);
lean_inc(v_quotContext_2051_);
v___x_2061_ = l_Lean_addMacroScope(v_quotContext_2051_, v___x_2060_, v_currMacroScope_2052_);
v___x_2062_ = lean_box(0);
lean_inc(v___x_2061_);
v___x_2063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2056_);
lean_ctor_set(v___x_2063_, 1, v___x_2059_);
lean_ctor_set(v___x_2063_, 2, v___x_2061_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__4));
lean_inc_ref_n(v___x_2038_, 9);
lean_inc_ref_n(v___x_2037_, 9);
lean_inc_ref_n(v___x_2036_, 9);
v___x_2065_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2064_);
v___x_2066_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2065_, v___x_2058_, v___x_2063_);
v___x_2067_ = l_Lean_SourceInfo_fromRef(v_ref_2050_, v___x_2035_);
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__5));
v___x_2069_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2068_);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__6));
lean_inc_n(v___x_2067_, 31);
v___x_2071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2067_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
lean_ctor_set(v___x_2072_, 1, v___x_2057_);
v___x_2073_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2067_);
lean_ctor_set(v___x_2073_, 1, v___x_2059_);
lean_ctor_set(v___x_2073_, 2, v___x_2061_);
lean_ctor_set(v___x_2073_, 3, v___x_2062_);
v___x_2074_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2067_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
v___x_2077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2067_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__8));
v___x_2079_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2078_);
v___x_2080_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__9));
v___x_2081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2067_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
v___x_2083_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2067_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
v___x_2085_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2086_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2067_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2086_);
v___x_2088_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__11));
v___x_2089_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2088_);
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2067_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2067_);
lean_ctor_set(v___x_2092_, 1, v___x_2088_);
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__12));
v___x_2094_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__13));
v___x_2096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2067_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__14));
v___x_2098_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2067_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2098_, v___x_2100_);
v___x_2102_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2101_);
v___x_2103_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__16));
v___x_2104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2067_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
lean_inc_ref_n(v___x_2087_, 2);
v___x_2105_ = l_Lean_Syntax_node5(v___x_2067_, v___x_2094_, v___x_2096_, v___x_2102_, v___x_2087_, v___x_2104_, v_a_2054_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2067_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
lean_inc_ref(v___x_2075_);
v___x_2108_ = l_Lean_Syntax_node5(v___x_2067_, v___x_2089_, v___x_2091_, v___x_2092_, v___x_2075_, v___x_2105_, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__17));
v___x_2111_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2110_);
v___x_2112_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2111_, v___x_2087_, v___x_2066_);
v___x_2113_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
v___x_2115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2067_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__19));
v___x_2117_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2116_);
v___x_2118_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__20));
v___x_2119_ = l_Lean_Name_mkStr4(v___x_2036_, v___x_2037_, v___x_2038_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
v___x_2121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2067_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2039_);
v___x_2123_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
v___x_2125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2067_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_Syntax_node4(v___x_2067_, v___x_2119_, v___x_2121_, v___x_2123_, v___x_2125_, v_body_2041_);
v___x_2127_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2126_);
v___x_2128_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2117_, v___x_2127_);
v___x_2129_ = l_Lean_Syntax_node6(v___x_2067_, v___x_2083_, v___x_2084_, v___x_2087_, v___x_2109_, v___x_2113_, v___x_2115_, v___x_2128_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v___x_2073_);
lean_inc_ref(v___x_2072_);
v___x_2130_ = l_Lean_Syntax_node5(v___x_2067_, v___x_2079_, v___x_2081_, v___x_2072_, v___x_2073_, v___x_2077_, v___x_2129_);
v___x_2131_ = l_Lean_Syntax_node7(v___x_2067_, v___x_2069_, v___x_2071_, v___x_2072_, v___x_2073_, v___x_2075_, v_rhs_2034_, v___x_2077_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2033_);
v___x_2133_ = lean_box(0);
v___x_2134_ = lean_box(v___x_2040_);
lean_inc(v___x_2131_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 12, 4);
lean_closure_set(v___f_2135_, 0, v___x_2131_);
lean_closure_set(v___f_2135_, 1, v___x_2132_);
lean_closure_set(v___f_2135_, 2, v___x_2134_);
lean_closure_set(v___f_2135_, 3, v___x_2133_);
lean_inc(v_ref_2050_);
v___x_2136_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2050_, v___x_2131_, v___f_2135_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_body_2041_);
lean_dec(v___x_2039_);
lean_dec_ref(v___x_2038_);
lean_dec_ref(v___x_2037_);
lean_dec_ref(v___x_2036_);
lean_dec(v_rhs_2034_);
lean_dec_ref(v_a_2033_);
v_a_2137_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2053_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2053_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object** _args){
lean_object* v_a_2145_ = _args[0];
lean_object* v_rhs_2146_ = _args[1];
lean_object* v___x_2147_ = _args[2];
lean_object* v___x_2148_ = _args[3];
lean_object* v___x_2149_ = _args[4];
lean_object* v___x_2150_ = _args[5];
lean_object* v___x_2151_ = _args[6];
lean_object* v___x_2152_ = _args[7];
lean_object* v_body_2153_ = _args[8];
lean_object* v___y_2154_ = _args[9];
lean_object* v___y_2155_ = _args[10];
lean_object* v___y_2156_ = _args[11];
lean_object* v___y_2157_ = _args[12];
lean_object* v___y_2158_ = _args[13];
lean_object* v___y_2159_ = _args[14];
lean_object* v___y_2160_ = _args[15];
lean_object* v___y_2161_ = _args[16];
_start:
{
uint8_t v___x_77853__boxed_2162_; uint8_t v___x_77858__boxed_2163_; lean_object* v_res_2164_; 
v___x_77853__boxed_2162_ = lean_unbox(v___x_2147_);
v___x_77858__boxed_2163_ = lean_unbox(v___x_2152_);
v_res_2164_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_a_2145_, v_rhs_2146_, v___x_77853__boxed_2162_, v___x_2148_, v___x_2149_, v___x_2150_, v___x_2151_, v___x_77858__boxed_2163_, v_body_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2165_, lean_object* v___y_2166_){
_start:
{
if (lean_obj_tag(v_x_2165_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v_x_2165_, 0);
lean_inc(v_a_2167_);
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2167_);
lean_ctor_set(v___x_2168_, 1, v___y_2166_);
return v___x_2168_;
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v_x_2165_, 0);
lean_inc(v_a_2169_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2169_);
lean_ctor_set(v___x_2170_, 1, v___y_2166_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2171_, v___y_2172_);
lean_dec_ref(v_x_2171_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2174_, lean_object* v_stx_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2174_, v_stx_2175_, v___y_2176_, v___y_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2178_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2189_);
v___x_2182_ = v___x_2178_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2178_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_a_2180_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_val_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2218_; 
v_val_2190_ = lean_ctor_get(v_a_2179_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2179_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2192_ = v_a_2179_;
v_isShared_2193_ = v_isSharedCheck_2218_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_val_2190_);
lean_dec(v_a_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2218_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v_snd_2194_; 
v_snd_2194_ = lean_ctor_get(v_val_2190_, 1);
lean_inc(v_snd_2194_);
lean_dec(v_val_2190_);
if (lean_obj_tag(v_snd_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
lean_del_object(v___x_2192_);
v_a_2195_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2178_);
v_a_2196_ = lean_ctor_get(v_snd_2194_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_snd_2194_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2198_ = v_snd_2194_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v_snd_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2201_, v_a_2195_);
lean_dec_ref(v___x_2201_);
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2217_; 
v_a_2205_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2178_);
v_a_2206_ = lean_ctor_get(v_snd_2194_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_snd_2194_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2208_ = v_snd_2194_;
v_isShared_2209_ = v_isSharedCheck_2217_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v_snd_2194_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2217_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_a_2206_);
v___x_2211_ = v___x_2192_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2213_, v_a_2205_);
lean_dec_ref(v___x_2213_);
return v___x_2214_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2219_ = lean_ctor_get(v___x_2178_, 0);
v_a_2220_ = lean_ctor_get(v___x_2178_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2178_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_inc(v_a_2219_);
lean_dec(v___x_2178_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2219_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2228_, lean_object* v_stx_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2228_, v_stx_2229_, v___y_2230_, v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_currNamespace_2233_);
lean_ctor_set(v___x_2236_, 1, v___y_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2241_, lean_object* v_currNamespace_2242_, lean_object* v_openDecls_2243_, lean_object* v_n_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = l_Lean_ResolveName_resolveNamespace(v_env_2241_, v_currNamespace_2242_, v_openDecls_2243_, v_n_2244_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2249_, lean_object* v_currNamespace_2250_, lean_object* v_openDecls_2251_, lean_object* v_n_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2249_, v_currNamespace_2250_, v_openDecls_2251_, v_n_2252_, v___y_2253_, v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2256_, lean_object* v_declName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v___x_2260_; lean_object* v_env_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; uint8_t v___x_2264_; 
v___x_2260_ = 0;
v_env_2261_ = l_Lean_Environment_setExporting(v_env_2256_, v___x_2260_);
lean_inc(v_declName_2257_);
v___x_2262_ = l_Lean_mkPrivateName(v_env_2261_, v_declName_2257_);
v___x_2263_ = 1;
lean_inc_ref(v_env_2261_);
v___x_2264_ = l_Lean_Environment_contains(v_env_2261_, v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = l_Lean_privateToUserName(v_declName_2257_);
v___x_2266_ = l_Lean_Environment_contains(v_env_2261_, v___x_2265_, v___x_2263_);
v___x_2267_ = lean_box(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___y_2259_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v_env_2261_);
lean_dec(v_declName_2257_);
v___x_2269_ = lean_box(v___x_2264_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___y_2259_);
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2271_, lean_object* v_declName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2271_, v_declName_2272_, v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2275_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2276_; double v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_float_of_nat(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2280_, lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_ref_2287_; lean_object* v___x_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2333_; 
v_ref_2287_ = lean_ctor_get(v___y_2284_, 5);
v___x_2288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2333_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2333_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v_traceState_2294_; lean_object* v_env_2295_; lean_object* v_nextMacroScope_2296_; lean_object* v_ngen_2297_; lean_object* v_auxDeclNGen_2298_; lean_object* v_cache_2299_; lean_object* v_messages_2300_; lean_object* v_infoState_2301_; lean_object* v_snapshotTasks_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2332_; 
v___x_2293_ = lean_st_ref_take(v___y_2285_);
v_traceState_2294_ = lean_ctor_get(v___x_2293_, 4);
v_env_2295_ = lean_ctor_get(v___x_2293_, 0);
v_nextMacroScope_2296_ = lean_ctor_get(v___x_2293_, 1);
v_ngen_2297_ = lean_ctor_get(v___x_2293_, 2);
v_auxDeclNGen_2298_ = lean_ctor_get(v___x_2293_, 3);
v_cache_2299_ = lean_ctor_get(v___x_2293_, 5);
v_messages_2300_ = lean_ctor_get(v___x_2293_, 6);
v_infoState_2301_ = lean_ctor_get(v___x_2293_, 7);
v_snapshotTasks_2302_ = lean_ctor_get(v___x_2293_, 8);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2304_ = v___x_2293_;
v_isShared_2305_ = v_isSharedCheck_2332_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snapshotTasks_2302_);
lean_inc(v_infoState_2301_);
lean_inc(v_messages_2300_);
lean_inc(v_cache_2299_);
lean_inc(v_traceState_2294_);
lean_inc(v_auxDeclNGen_2298_);
lean_inc(v_ngen_2297_);
lean_inc(v_nextMacroScope_2296_);
lean_inc(v_env_2295_);
lean_dec(v___x_2293_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2332_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint64_t v_tid_2306_; lean_object* v_traces_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2331_; 
v_tid_2306_ = lean_ctor_get_uint64(v_traceState_2294_, sizeof(void*)*1);
v_traces_2307_ = lean_ctor_get(v_traceState_2294_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_traceState_2294_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2309_ = v_traceState_2294_;
v_isShared_2310_ = v_isSharedCheck_2331_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_traces_2307_);
lean_dec(v_traceState_2294_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2331_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; double v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2313_ = 0;
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2315_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2315_, 0, v_cls_2280_);
lean_ctor_set(v___x_2315_, 1, v___x_2311_);
lean_ctor_set(v___x_2315_, 2, v___x_2314_);
lean_ctor_set_float(v___x_2315_, sizeof(void*)*3, v___x_2312_);
lean_ctor_set_float(v___x_2315_, sizeof(void*)*3 + 8, v___x_2312_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*3 + 16, v___x_2313_);
v___x_2316_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2317_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v_a_2289_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
lean_inc(v_ref_2287_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_ref_2287_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_PersistentArray_push___redArg(v_traces_2307_, v___x_2318_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2319_);
v___x_2321_ = v___x_2309_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2319_);
lean_ctor_set_uint64(v_reuseFailAlloc_2330_, sizeof(void*)*1, v_tid_2306_);
v___x_2321_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 4, v___x_2321_);
v___x_2323_ = v___x_2304_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_env_2295_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_nextMacroScope_2296_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_ngen_2297_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_auxDeclNGen_2298_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2329_, 5, v_cache_2299_);
lean_ctor_set(v_reuseFailAlloc_2329_, 6, v_messages_2300_);
lean_ctor_set(v_reuseFailAlloc_2329_, 7, v_infoState_2301_);
lean_ctor_set(v_reuseFailAlloc_2329_, 8, v_snapshotTasks_2302_);
v___x_2323_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_st_ref_set(v___y_2285_, v___x_2323_);
v___x_2325_ = lean_box(0);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2325_);
v___x_2327_ = v___x_2291_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2334_, lean_object* v_msg_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2334_, v_msg_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
if (lean_obj_tag(v_as_2345_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
else
{
lean_object* v_options_2356_; uint8_t v_hasTrace_2357_; 
v_options_2356_ = lean_ctor_get(v___y_2351_, 2);
v_hasTrace_2357_ = lean_ctor_get_uint8(v_options_2356_, sizeof(void*)*1);
if (v_hasTrace_2357_ == 0)
{
lean_object* v_tail_2358_; 
v_tail_2358_ = lean_ctor_get(v_as_2345_, 1);
lean_inc(v_tail_2358_);
lean_dec_ref(v_as_2345_);
v_as_2345_ = v_tail_2358_;
goto _start;
}
else
{
lean_object* v_head_2360_; lean_object* v_tail_2361_; lean_object* v_fst_2362_; lean_object* v_snd_2363_; lean_object* v_inheritedTraceOptions_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_head_2360_ = lean_ctor_get(v_as_2345_, 0);
lean_inc(v_head_2360_);
v_tail_2361_ = lean_ctor_get(v_as_2345_, 1);
lean_inc(v_tail_2361_);
lean_dec_ref(v_as_2345_);
v_fst_2362_ = lean_ctor_get(v_head_2360_, 0);
lean_inc_n(v_fst_2362_, 2);
v_snd_2363_ = lean_ctor_get(v_head_2360_, 1);
lean_inc(v_snd_2363_);
lean_dec(v_head_2360_);
v_inheritedTraceOptions_2364_ = lean_ctor_get(v___y_2351_, 13);
v___x_2365_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2366_ = l_Lean_Name_append(v___x_2365_, v_fst_2362_);
v___x_2367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2364_, v_options_2356_, v___x_2366_);
lean_dec(v___x_2366_);
if (v___x_2367_ == 0)
{
lean_dec(v_snd_2363_);
lean_dec(v_fst_2362_);
v_as_2345_ = v_tail_2361_;
goto _start;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_snd_2363_);
v___x_2370_ = l_Lean_MessageData_ofFormat(v___x_2369_);
v___x_2371_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2362_, v___x_2370_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_dec_ref(v___x_2371_);
v_as_2345_ = v_tail_2361_;
goto _start;
}
else
{
lean_dec(v_tail_2361_);
return v___x_2371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2393_, lean_object* v_i_2394_, lean_object* v_k_2395_){
_start:
{
uint8_t v_res_2396_; lean_object* v_r_2397_; 
v_res_2396_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2393_, v_i_2394_, v_k_2395_);
lean_dec_ref(v_k_2395_);
lean_dec_ref(v_keys_2393_);
v_r_2397_ = lean_box(v_res_2396_);
return v_r_2397_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2398_, size_t v_x_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 0)
{
lean_object* v_es_2401_; lean_object* v___x_2402_; size_t v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; lean_object* v_j_2406_; lean_object* v___x_2407_; 
v_es_2401_ = lean_ctor_get(v_x_2398_, 0);
v___x_2402_ = lean_box(2);
v___x_2403_ = ((size_t)5ULL);
v___x_2404_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2405_ = lean_usize_land(v_x_2399_, v___x_2404_);
v_j_2406_ = lean_usize_to_nat(v___x_2405_);
v___x_2407_ = lean_array_get_borrowed(v___x_2402_, v_es_2401_, v_j_2406_);
lean_dec(v_j_2406_);
switch(lean_obj_tag(v___x_2407_))
{
case 0:
{
lean_object* v_key_2408_; uint8_t v___x_2409_; 
v_key_2408_ = lean_ctor_get(v___x_2407_, 0);
v___x_2409_ = l_Lean_instBEqExtraModUse_beq(v_x_2400_, v_key_2408_);
return v___x_2409_;
}
case 1:
{
lean_object* v_node_2410_; size_t v___x_2411_; 
v_node_2410_ = lean_ctor_get(v___x_2407_, 0);
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
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2414_, v___x_2415_, v_x_2400_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2417_, lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
size_t v_x_78453__boxed_2420_; uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_x_78453__boxed_2420_ = lean_unbox_usize(v_x_2418_);
lean_dec(v_x_2418_);
v_res_2421_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2417_, v_x_78453__boxed_2420_, v_x_2419_);
lean_dec_ref(v_x_2419_);
lean_dec_ref(v_x_2417_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2423_, lean_object* v_x_2424_){
_start:
{
uint64_t v___x_2425_; size_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2425_ = l_Lean_instHashableExtraModUse_hash(v_x_2424_);
v___x_2426_ = lean_uint64_to_usize(v___x_2425_);
v___x_2427_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2423_, v___x_2426_, v_x_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
uint8_t v_res_2430_; lean_object* v_r_2431_; 
v_res_2430_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2428_, v_x_2429_);
lean_dec_ref(v_x_2429_);
lean_dec_ref(v_x_2428_);
v_r_2431_ = lean_box(v_res_2430_);
return v_r_2431_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2436_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_cls_2455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2456_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2457_ = l_Lean_Name_append(v___x_2456_, v_cls_2455_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2463_ = l_Lean_stringToMessageData(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2468_, uint8_t v_isMeta_2469_, lean_object* v_hint_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v_env_2480_; uint8_t v_isExporting_2481_; lean_object* v___x_2482_; lean_object* v_env_2483_; lean_object* v___x_2484_; lean_object* v_entry_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2479_ = lean_st_ref_get(v___y_2477_);
v_env_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_env_2480_);
lean_dec(v___x_2479_);
v_isExporting_2481_ = lean_ctor_get_uint8(v_env_2480_, sizeof(void*)*8);
lean_dec_ref(v_env_2480_);
v___x_2482_ = lean_st_ref_get(v___y_2477_);
v_env_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_ref(v_env_2483_);
lean_dec(v___x_2482_);
v___x_2484_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2468_);
v_entry_2485_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2485_, 0, v_mod_2468_);
lean_ctor_set_uint8(v_entry_2485_, sizeof(void*)*1, v_isExporting_2481_);
lean_ctor_set_uint8(v_entry_2485_, sizeof(void*)*1 + 1, v_isMeta_2469_);
v___x_2486_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2487_ = lean_box(1);
v___x_2488_ = lean_box(0);
v___x_2531_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2484_, v___x_2486_, v_env_2483_, v___x_2487_, v___x_2488_);
v___x_2532_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2531_, v_entry_2485_);
lean_dec(v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v_options_2533_; uint8_t v_hasTrace_2534_; 
v_options_2533_ = lean_ctor_get(v___y_2476_, 2);
v_hasTrace_2534_ = lean_ctor_get_uint8(v_options_2533_, sizeof(void*)*1);
if (v_hasTrace_2534_ == 0)
{
lean_dec(v_hint_2470_);
lean_dec(v_mod_2468_);
v___y_2490_ = v___y_2475_;
v___y_2491_ = v___y_2477_;
goto v___jp_2489_;
}
else
{
lean_object* v_inheritedTraceOptions_2535_; lean_object* v_cls_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_inheritedTraceOptions_2535_ = lean_ctor_get(v___y_2476_, 13);
v_cls_2536_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2556_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2535_, v_options_2533_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_dec(v_hint_2470_);
lean_dec(v_mod_2468_);
v___y_2490_ = v___y_2475_;
v___y_2491_ = v___y_2477_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2558_; lean_object* v___y_2560_; 
v___x_2558_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2481_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2560_ = v___x_2567_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2560_ = v___x_2568_;
goto v___jp_2559_;
}
v___jp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_inc_ref(v___y_2560_);
v___x_2561_ = l_Lean_stringToMessageData(v___y_2560_);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2558_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
if (v_isMeta_2469_ == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2543_ = v___x_2564_;
v___y_2544_ = v___x_2565_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2543_ = v___x_2564_;
v___y_2544_ = v___x_2566_;
goto v___jp_2542_;
}
}
}
v___jp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___y_2538_);
lean_ctor_set(v___x_2540_, 1, v___y_2539_);
v___x_2541_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2536_, v___x_2540_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref(v___x_2541_);
v___y_2490_ = v___y_2475_;
v___y_2491_ = v___y_2477_;
goto v___jp_2489_;
}
else
{
lean_dec_ref(v_entry_2485_);
return v___x_2541_;
}
}
v___jp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
lean_inc_ref(v___y_2544_);
v___x_2545_ = l_Lean_stringToMessageData(v___y_2544_);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___y_2543_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = l_Lean_MessageData_ofName(v_mod_2468_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_Name_isAnonymous(v_hint_2470_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2553_ = l_Lean_MessageData_ofName(v_hint_2470_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___y_2538_ = v___x_2550_;
v___y_2539_ = v___x_2554_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2555_; 
lean_dec(v_hint_2470_);
v___x_2555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2538_ = v___x_2550_;
v___y_2539_ = v___x_2555_;
goto v___jp_2537_;
}
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_entry_2485_);
lean_dec(v_hint_2470_);
lean_dec(v_mod_2468_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
v___jp_2489_:
{
lean_object* v___x_2492_; lean_object* v_toEnvExtension_2493_; lean_object* v_env_2494_; lean_object* v_nextMacroScope_2495_; lean_object* v_ngen_2496_; lean_object* v_auxDeclNGen_2497_; lean_object* v_traceState_2498_; lean_object* v_messages_2499_; lean_object* v_infoState_2500_; lean_object* v_snapshotTasks_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2529_; 
v___x_2492_ = lean_st_ref_take(v___y_2491_);
v_toEnvExtension_2493_ = lean_ctor_get(v___x_2486_, 0);
v_env_2494_ = lean_ctor_get(v___x_2492_, 0);
v_nextMacroScope_2495_ = lean_ctor_get(v___x_2492_, 1);
v_ngen_2496_ = lean_ctor_get(v___x_2492_, 2);
v_auxDeclNGen_2497_ = lean_ctor_get(v___x_2492_, 3);
v_traceState_2498_ = lean_ctor_get(v___x_2492_, 4);
v_messages_2499_ = lean_ctor_get(v___x_2492_, 6);
v_infoState_2500_ = lean_ctor_get(v___x_2492_, 7);
v_snapshotTasks_2501_ = lean_ctor_get(v___x_2492_, 8);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v___x_2492_, 5);
lean_dec(v_unused_2530_);
v___x_2503_ = v___x_2492_;
v_isShared_2504_ = v_isSharedCheck_2529_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_snapshotTasks_2501_);
lean_inc(v_infoState_2500_);
lean_inc(v_messages_2499_);
lean_inc(v_traceState_2498_);
lean_inc(v_auxDeclNGen_2497_);
lean_inc(v_ngen_2496_);
lean_inc(v_nextMacroScope_2495_);
lean_inc(v_env_2494_);
lean_dec(v___x_2492_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2529_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_asyncMode_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v_asyncMode_2505_ = lean_ctor_get(v_toEnvExtension_2493_, 2);
v___x_2506_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2486_, v_env_2494_, v_entry_2485_, v_asyncMode_2505_, v___x_2488_);
v___x_2507_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 5, v___x_2507_);
lean_ctor_set(v___x_2503_, 0, v___x_2506_);
v___x_2509_ = v___x_2503_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_nextMacroScope_2495_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_ngen_2496_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_auxDeclNGen_2497_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_traceState_2498_);
lean_ctor_set(v_reuseFailAlloc_2528_, 5, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2528_, 6, v_messages_2499_);
lean_ctor_set(v_reuseFailAlloc_2528_, 7, v_infoState_2500_);
lean_ctor_set(v_reuseFailAlloc_2528_, 8, v_snapshotTasks_2501_);
v___x_2509_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_mctx_2512_; lean_object* v_zetaDeltaFVarIds_2513_; lean_object* v_postponed_2514_; lean_object* v_diag_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2526_; 
v___x_2510_ = lean_st_ref_set(v___y_2491_, v___x_2509_);
v___x_2511_ = lean_st_ref_take(v___y_2490_);
v_mctx_2512_ = lean_ctor_get(v___x_2511_, 0);
v_zetaDeltaFVarIds_2513_ = lean_ctor_get(v___x_2511_, 2);
v_postponed_2514_ = lean_ctor_get(v___x_2511_, 3);
v_diag_2515_ = lean_ctor_get(v___x_2511_, 4);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2511_, 1);
lean_dec(v_unused_2527_);
v___x_2517_ = v___x_2511_;
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_diag_2515_);
lean_inc(v_postponed_2514_);
lean_inc(v_zetaDeltaFVarIds_2513_);
lean_inc(v_mctx_2512_);
lean_dec(v___x_2511_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_mctx_2512_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_zetaDeltaFVarIds_2513_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_postponed_2514_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_diag_2515_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_st_ref_set(v___y_2490_, v___x_2521_);
v___x_2523_ = lean_box(0);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2571_, lean_object* v_isMeta_2572_, lean_object* v_hint_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v_isMeta_boxed_2582_; lean_object* v_res_2583_; 
v_isMeta_boxed_2582_ = lean_unbox(v_isMeta_2572_);
v_res_2583_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2571_, v_isMeta_boxed_2582_, v_hint_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2584_, lean_object* v_declName_2585_, lean_object* v_as_2586_, size_t v_sz_2587_, size_t v_i_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_usize_dec_lt(v_i_2588_, v_sz_2587_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
lean_dec(v_declName_2585_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_b_2589_);
return v___x_2599_;
}
else
{
lean_object* v___x_2600_; lean_object* v_modules_2601_; lean_object* v___x_2602_; lean_object* v_a_2603_; lean_object* v___x_2604_; lean_object* v_toImport_2605_; lean_object* v_module_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2600_ = l_Lean_Environment_header(v___x_2584_);
v_modules_2601_ = lean_ctor_get(v___x_2600_, 3);
lean_inc_ref(v_modules_2601_);
lean_dec_ref(v___x_2600_);
v___x_2602_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2603_ = lean_array_uget_borrowed(v_as_2586_, v_i_2588_);
v___x_2604_ = lean_array_get(v___x_2602_, v_modules_2601_, v_a_2603_);
lean_dec_ref(v_modules_2601_);
v_toImport_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc_ref(v_toImport_2605_);
lean_dec(v___x_2604_);
v_module_2606_ = lean_ctor_get(v_toImport_2605_, 0);
lean_inc(v_module_2606_);
lean_dec_ref(v_toImport_2605_);
v___x_2607_ = 0;
lean_inc(v_declName_2585_);
v___x_2608_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2606_, v___x_2607_, v_declName_2585_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v___x_2609_; size_t v___x_2610_; size_t v___x_2611_; 
lean_dec_ref(v___x_2608_);
v___x_2609_ = lean_box(0);
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_add(v_i_2588_, v___x_2610_);
v_i_2588_ = v___x_2611_;
v_b_2589_ = v___x_2609_;
goto _start;
}
else
{
lean_dec(v_declName_2585_);
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2613_, lean_object* v_declName_2614_, lean_object* v_as_2615_, lean_object* v_sz_2616_, lean_object* v_i_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
size_t v_sz_boxed_2627_; size_t v_i_boxed_2628_; lean_object* v_res_2629_; 
v_sz_boxed_2627_ = lean_unbox_usize(v_sz_2616_);
lean_dec(v_sz_2616_);
v_i_boxed_2628_ = lean_unbox_usize(v_i_2617_);
lean_dec(v_i_2617_);
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2613_, v_declName_2614_, v_as_2615_, v_sz_boxed_2627_, v_i_boxed_2628_, v_b_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec_ref(v_as_2615_);
lean_dec_ref(v___x_2613_);
return v_res_2629_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2633_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2634_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2633_, v___x_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2637_, uint8_t v_isMeta_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; lean_object* v_env_2651_; lean_object* v___y_2653_; lean_object* v___x_2666_; 
v___x_2647_ = lean_st_ref_get(v___y_2645_);
v_env_2651_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_ref(v_env_2651_);
lean_dec(v___x_2647_);
v___x_2666_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2651_, v_declName_2637_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec_ref(v_env_2651_);
lean_dec(v_declName_2637_);
goto v___jp_2648_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; lean_object* v_modules_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_val_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v___x_2666_);
v___x_2668_ = l_Lean_Environment_header(v_env_2651_);
v_modules_2669_ = lean_ctor_get(v___x_2668_, 3);
lean_inc_ref(v_modules_2669_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = lean_array_get_size(v_modules_2669_);
v___x_2671_ = lean_nat_dec_lt(v_val_2667_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec_ref(v_modules_2669_);
lean_dec(v_val_2667_);
lean_dec_ref(v_env_2651_);
lean_dec(v_declName_2637_);
goto v___jp_2648_;
}
else
{
lean_object* v___x_2672_; lean_object* v_env_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___y_2677_; 
v___x_2672_ = lean_st_ref_get(v___y_2645_);
v_env_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref(v_env_2673_);
lean_dec(v___x_2672_);
v___x_2674_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2675_ = lean_array_fget(v_modules_2669_, v_val_2667_);
lean_dec(v_val_2667_);
lean_dec_ref(v_modules_2669_);
if (v_isMeta_2638_ == 0)
{
lean_dec_ref(v_env_2673_);
v___y_2677_ = v_isMeta_2638_;
goto v___jp_2676_;
}
else
{
uint8_t v___x_2688_; 
lean_inc(v_declName_2637_);
v___x_2688_ = l_Lean_isMarkedMeta(v_env_2673_, v_declName_2637_);
if (v___x_2688_ == 0)
{
v___y_2677_ = v_isMeta_2638_;
goto v___jp_2676_;
}
else
{
uint8_t v___x_2689_; 
v___x_2689_ = 0;
v___y_2677_ = v___x_2689_;
goto v___jp_2676_;
}
}
v___jp_2676_:
{
lean_object* v_toImport_2678_; lean_object* v_module_2679_; lean_object* v___x_2680_; 
v_toImport_2678_ = lean_ctor_get(v___x_2675_, 0);
lean_inc_ref(v_toImport_2678_);
lean_dec(v___x_2675_);
v_module_2679_ = lean_ctor_get(v_toImport_2678_, 0);
lean_inc(v_module_2679_);
lean_dec_ref(v_toImport_2678_);
lean_inc(v_declName_2637_);
v___x_2680_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2679_, v___y_2677_, v_declName_2637_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec_ref(v___x_2680_);
v___x_2681_ = l_Lean_indirectModUseExt;
v___x_2682_ = lean_box(1);
v___x_2683_ = lean_box(0);
lean_inc_ref(v_env_2651_);
v___x_2684_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2674_, v___x_2681_, v_env_2651_, v___x_2682_, v___x_2683_);
v___x_2685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_2684_, v_declName_2637_);
lean_dec(v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2653_ = v___x_2686_;
goto v___jp_2652_;
}
else
{
lean_object* v_val_2687_; 
v_val_2687_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_val_2687_);
lean_dec_ref(v___x_2685_);
v___y_2653_ = v_val_2687_;
goto v___jp_2652_;
}
}
else
{
lean_dec_ref(v_env_2651_);
lean_dec(v_declName_2637_);
return v___x_2680_;
}
}
}
}
v___jp_2648_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; size_t v_sz_2655_; size_t v___x_2656_; lean_object* v___x_2657_; 
v___x_2654_ = lean_box(0);
v_sz_2655_ = lean_array_size(v___y_2653_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2651_, v_declName_2637_, v___y_2653_, v_sz_2655_, v___x_2656_, v___x_2654_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_env_2651_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2657_, 0);
lean_dec(v_unused_2665_);
v___x_2659_ = v___x_2657_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_dec(v___x_2657_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2654_);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2654_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2690_, lean_object* v_isMeta_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
uint8_t v_isMeta_boxed_2700_; lean_object* v_res_2701_; 
v_isMeta_boxed_2700_ = lean_unbox(v_isMeta_2691_);
v_res_2701_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2690_, v_isMeta_boxed_2700_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
if (lean_obj_tag(v_as_x27_2702_) == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v_b_2703_);
return v___x_2712_;
}
else
{
lean_object* v_head_2713_; lean_object* v_tail_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; 
v_head_2713_ = lean_ctor_get(v_as_x27_2702_, 0);
lean_inc(v_head_2713_);
v_tail_2714_ = lean_ctor_get(v_as_x27_2702_, 1);
lean_inc(v_tail_2714_);
lean_dec_ref(v_as_x27_2702_);
v___x_2715_ = 1;
v___x_2716_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2713_, v___x_2715_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v___x_2717_; 
lean_dec_ref(v___x_2716_);
v___x_2717_ = lean_box(0);
v_as_x27_2702_ = v_tail_2714_;
v_b_2703_ = v___x_2717_;
goto _start;
}
else
{
lean_dec(v_tail_2714_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2719_, v_b_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2730_, lean_object* v_options_2731_, lean_object* v_currNamespace_2732_, lean_object* v_openDecls_2733_, lean_object* v_n_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = l_Lean_ResolveName_resolveGlobalName(v_env_2730_, v_options_2731_, v_currNamespace_2732_, v_openDecls_2733_, v_n_2734_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2739_, lean_object* v_options_2740_, lean_object* v_currNamespace_2741_, lean_object* v_openDecls_2742_, lean_object* v_n_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2739_, v_options_2740_, v_currNamespace_2741_, v_openDecls_2742_, v_n_2743_, v___y_2744_, v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v_options_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(lean_object* v_msg_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_ref_2753_; lean_object* v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2763_; 
v_ref_2753_ = lean_ctor_get(v___y_2750_, 5);
v___x_2754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
lean_inc(v_ref_2753_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_ref_2753_);
lean_ctor_set(v___x_2759_, 1, v_a_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 1);
lean_ctor_set(v___x_2757_, 0, v___x_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg___boxed(lean_object* v_msg_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(v_msg_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_2771_, lean_object* v_msg_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_fileName_2781_; lean_object* v_fileMap_2782_; lean_object* v_options_2783_; lean_object* v_currRecDepth_2784_; lean_object* v_maxRecDepth_2785_; lean_object* v_ref_2786_; lean_object* v_currNamespace_2787_; lean_object* v_openDecls_2788_; lean_object* v_initHeartbeats_2789_; lean_object* v_maxHeartbeats_2790_; lean_object* v_quotContext_2791_; lean_object* v_currMacroScope_2792_; uint8_t v_diag_2793_; lean_object* v_cancelTk_x3f_2794_; uint8_t v_suppressElabErrors_2795_; lean_object* v_inheritedTraceOptions_2796_; lean_object* v_ref_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_fileName_2781_ = lean_ctor_get(v___y_2778_, 0);
v_fileMap_2782_ = lean_ctor_get(v___y_2778_, 1);
v_options_2783_ = lean_ctor_get(v___y_2778_, 2);
v_currRecDepth_2784_ = lean_ctor_get(v___y_2778_, 3);
v_maxRecDepth_2785_ = lean_ctor_get(v___y_2778_, 4);
v_ref_2786_ = lean_ctor_get(v___y_2778_, 5);
v_currNamespace_2787_ = lean_ctor_get(v___y_2778_, 6);
v_openDecls_2788_ = lean_ctor_get(v___y_2778_, 7);
v_initHeartbeats_2789_ = lean_ctor_get(v___y_2778_, 8);
v_maxHeartbeats_2790_ = lean_ctor_get(v___y_2778_, 9);
v_quotContext_2791_ = lean_ctor_get(v___y_2778_, 10);
v_currMacroScope_2792_ = lean_ctor_get(v___y_2778_, 11);
v_diag_2793_ = lean_ctor_get_uint8(v___y_2778_, sizeof(void*)*14);
v_cancelTk_x3f_2794_ = lean_ctor_get(v___y_2778_, 12);
v_suppressElabErrors_2795_ = lean_ctor_get_uint8(v___y_2778_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2796_ = lean_ctor_get(v___y_2778_, 13);
v_ref_2797_ = l_Lean_replaceRef(v_ref_2771_, v_ref_2786_);
lean_inc_ref(v_inheritedTraceOptions_2796_);
lean_inc(v_cancelTk_x3f_2794_);
lean_inc(v_currMacroScope_2792_);
lean_inc(v_quotContext_2791_);
lean_inc(v_maxHeartbeats_2790_);
lean_inc(v_initHeartbeats_2789_);
lean_inc(v_openDecls_2788_);
lean_inc(v_currNamespace_2787_);
lean_inc(v_maxRecDepth_2785_);
lean_inc(v_currRecDepth_2784_);
lean_inc_ref(v_options_2783_);
lean_inc_ref(v_fileMap_2782_);
lean_inc_ref(v_fileName_2781_);
v___x_2798_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2798_, 0, v_fileName_2781_);
lean_ctor_set(v___x_2798_, 1, v_fileMap_2782_);
lean_ctor_set(v___x_2798_, 2, v_options_2783_);
lean_ctor_set(v___x_2798_, 3, v_currRecDepth_2784_);
lean_ctor_set(v___x_2798_, 4, v_maxRecDepth_2785_);
lean_ctor_set(v___x_2798_, 5, v_ref_2797_);
lean_ctor_set(v___x_2798_, 6, v_currNamespace_2787_);
lean_ctor_set(v___x_2798_, 7, v_openDecls_2788_);
lean_ctor_set(v___x_2798_, 8, v_initHeartbeats_2789_);
lean_ctor_set(v___x_2798_, 9, v_maxHeartbeats_2790_);
lean_ctor_set(v___x_2798_, 10, v_quotContext_2791_);
lean_ctor_set(v___x_2798_, 11, v_currMacroScope_2792_);
lean_ctor_set(v___x_2798_, 12, v_cancelTk_x3f_2794_);
lean_ctor_set(v___x_2798_, 13, v_inheritedTraceOptions_2796_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*14, v_diag_2793_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*14 + 1, v_suppressElabErrors_2795_);
v___x_2799_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(v_msg_2772_, v___y_2776_, v___y_2777_, v___x_2798_, v___y_2779_);
lean_dec_ref(v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2800_, lean_object* v_msg_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_2800_, v_msg_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v_ref_2800_);
return v_res_2810_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = l_Lean_maxRecDepthErrorMessage;
v___x_2817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
return v___x_2817_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_2819_ = l_Lean_MessageData_ofFormat(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_2821_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_2822_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_ref_2823_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v_env_2842_; lean_object* v_options_2843_; lean_object* v_currRecDepth_2844_; lean_object* v_maxRecDepth_2845_; lean_object* v_ref_2846_; lean_object* v_currNamespace_2847_; lean_object* v_openDecls_2848_; lean_object* v_quotContext_2849_; lean_object* v_currMacroScope_2850_; lean_object* v___x_2851_; lean_object* v_nextMacroScope_2852_; lean_object* v___f_2853_; lean_object* v___f_2854_; lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v_methods_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2841_ = lean_st_ref_get(v___y_2839_);
v_env_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc_ref_n(v_env_2842_, 4);
lean_dec(v___x_2841_);
v_options_2843_ = lean_ctor_get(v___y_2838_, 2);
v_currRecDepth_2844_ = lean_ctor_get(v___y_2838_, 3);
v_maxRecDepth_2845_ = lean_ctor_get(v___y_2838_, 4);
v_ref_2846_ = lean_ctor_get(v___y_2838_, 5);
v_currNamespace_2847_ = lean_ctor_get(v___y_2838_, 6);
v_openDecls_2848_ = lean_ctor_get(v___y_2838_, 7);
v_quotContext_2849_ = lean_ctor_get(v___y_2838_, 10);
v_currMacroScope_2850_ = lean_ctor_get(v___y_2838_, 11);
v___x_2851_ = lean_st_ref_get(v___y_2839_);
v_nextMacroScope_2852_ = lean_ctor_get(v___x_2851_, 1);
lean_inc(v_nextMacroScope_2852_);
lean_dec(v___x_2851_);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2853_, 0, v_env_2842_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2854_, 0, v_env_2842_);
lean_inc_n(v_openDecls_2848_, 2);
lean_inc_n(v_currNamespace_2847_, 3);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2855_, 0, v_env_2842_);
lean_closure_set(v___f_2855_, 1, v_currNamespace_2847_);
lean_closure_set(v___f_2855_, 2, v_openDecls_2848_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2856_, 0, v_currNamespace_2847_);
lean_inc_ref(v_options_2843_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2857_, 0, v_env_2842_);
lean_closure_set(v___f_2857_, 1, v_options_2843_);
lean_closure_set(v___f_2857_, 2, v_currNamespace_2847_);
lean_closure_set(v___f_2857_, 3, v_openDecls_2848_);
v_methods_2858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2858_, 0, v___f_2853_);
lean_ctor_set(v_methods_2858_, 1, v___f_2856_);
lean_ctor_set(v_methods_2858_, 2, v___f_2854_);
lean_ctor_set(v_methods_2858_, 3, v___f_2855_);
lean_ctor_set(v_methods_2858_, 4, v___f_2857_);
lean_inc(v_ref_2846_);
lean_inc(v_maxRecDepth_2845_);
lean_inc(v_currRecDepth_2844_);
lean_inc(v_currMacroScope_2850_);
lean_inc(v_quotContext_2849_);
v___x_2859_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2859_, 0, v_methods_2858_);
lean_ctor_set(v___x_2859_, 1, v_quotContext_2849_);
lean_ctor_set(v___x_2859_, 2, v_currMacroScope_2850_);
lean_ctor_set(v___x_2859_, 3, v_currRecDepth_2844_);
lean_ctor_set(v___x_2859_, 4, v_maxRecDepth_2845_);
lean_ctor_set(v___x_2859_, 5, v_ref_2846_);
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2861_, 0, v_nextMacroScope_2852_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
lean_ctor_set(v___x_2861_, 2, v___x_2860_);
v___x_2862_ = lean_apply_2(v_x_2832_, v___x_2859_, v___x_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v_a_2864_; lean_object* v_macroScope_2865_; lean_object* v_traceMsgs_2866_; lean_object* v_expandedMacroDecls_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 1);
lean_inc(v_a_2863_);
v_a_2864_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2862_);
v_macroScope_2865_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_macroScope_2865_);
v_traceMsgs_2866_ = lean_ctor_get(v_a_2863_, 1);
lean_inc(v_traceMsgs_2866_);
v_expandedMacroDecls_2867_ = lean_ctor_get(v_a_2863_, 2);
lean_inc(v_expandedMacroDecls_2867_);
lean_dec(v_a_2863_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_2867_, v___x_2868_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2870_; lean_object* v_env_2871_; lean_object* v_ngen_2872_; lean_object* v_auxDeclNGen_2873_; lean_object* v_traceState_2874_; lean_object* v_cache_2875_; lean_object* v_messages_2876_; lean_object* v_infoState_2877_; lean_object* v_snapshotTasks_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___x_2869_);
v___x_2870_ = lean_st_ref_take(v___y_2839_);
v_env_2871_ = lean_ctor_get(v___x_2870_, 0);
v_ngen_2872_ = lean_ctor_get(v___x_2870_, 2);
v_auxDeclNGen_2873_ = lean_ctor_get(v___x_2870_, 3);
v_traceState_2874_ = lean_ctor_get(v___x_2870_, 4);
v_cache_2875_ = lean_ctor_get(v___x_2870_, 5);
v_messages_2876_ = lean_ctor_get(v___x_2870_, 6);
v_infoState_2877_ = lean_ctor_get(v___x_2870_, 7);
v_snapshotTasks_2878_ = lean_ctor_get(v___x_2870_, 8);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v___x_2870_, 1);
lean_dec(v_unused_2905_);
v___x_2880_ = v___x_2870_;
v_isShared_2881_ = v_isSharedCheck_2904_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_snapshotTasks_2878_);
lean_inc(v_infoState_2877_);
lean_inc(v_messages_2876_);
lean_inc(v_cache_2875_);
lean_inc(v_traceState_2874_);
lean_inc(v_auxDeclNGen_2873_);
lean_inc(v_ngen_2872_);
lean_inc(v_env_2871_);
lean_dec(v___x_2870_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2904_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 1, v_macroScope_2865_);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2871_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_macroScope_2865_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2872_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2873_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_traceState_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_messages_2876_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_infoState_2877_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_snapshotTasks_2878_);
v___x_2883_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_st_ref_set(v___y_2839_, v___x_2883_);
v___x_2885_ = l_List_reverse___redArg(v_traceMsgs_2866_);
v___x_2886_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_2885_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2894_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v_a_2864_);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2864_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2864_);
v_a_2895_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_traceMsgs_2866_);
lean_dec(v_macroScope_2865_);
lean_dec(v_a_2864_);
v_a_2906_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2869_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2869_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2862_);
if (lean_obj_tag(v_a_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v_a_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_a_2915_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_a_2915_);
v_a_2916_ = lean_ctor_get(v_a_2914_, 1);
lean_inc_ref(v_a_2916_);
lean_dec_ref(v_a_2914_);
v___x_2917_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_2918_ = lean_string_dec_eq(v_a_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2916_);
v___x_2920_ = l_Lean_MessageData_ofFormat(v___x_2919_);
v___x_2921_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_2915_, v___x_2920_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v_a_2915_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_a_2916_);
v___x_2922_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_2915_);
return v___x_2922_;
}
}
else
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_2923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_quotContext_2938_; lean_object* v_currMacroScope_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_quotContext_2938_ = lean_ctor_get(v___y_2935_, 10);
lean_inc(v_quotContext_2938_);
v_currMacroScope_2939_ = lean_ctor_get(v___y_2935_, 11);
lean_inc(v_currMacroScope_2939_);
lean_dec_ref(v___y_2935_);
v___x_2940_ = l_Lean_addMacroScope(v_quotContext_2938_, v___x_2934_, v_currMacroScope_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; 
v___f_2955_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_2956_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2955_, v___y_2952_, v___y_2953_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_2961_, uint8_t v_canonical_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_2968_, v___y_2969_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = l_Lean_mkIdentFrom(v_ref_2961_, v_a_2972_, v_canonical_2962_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_a_2981_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2971_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2971_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_2989_, lean_object* v_canonical_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v_canonical_boxed_2999_; lean_object* v_res_3000_; 
v_canonical_boxed_2999_ = lean_unbox(v_canonical_2990_);
v_res_3000_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_2989_, v_canonical_boxed_2999_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v_ref_2989_);
return v_res_3000_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3013_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3014_ = l_Lean_Name_append(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3017_ = l_Lean_stringToMessageData(v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_letOrReassign_3024_, lean_object* v_decl_3025_, lean_object* v_dec_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_letOrReassign_3024_, v_decl_3025_, v_dec_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec_ref(v_a_3027_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_letOrReassign_3036_, lean_object* v_decl_3037_, lean_object* v_dec_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; 
lean_inc(v_decl_3037_);
v___x_3047_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3037_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3036_, v_a_3048_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; 
lean_dec_ref(v___x_3049_);
v___x_3050_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3036_, v_decl_3037_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v_doBlockResultType_3052_; lean_object* v___x_3053_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v_doBlockResultType_3052_ = lean_ctor_get(v_a_3039_, 3);
lean_inc_ref(v_doBlockResultType_3052_);
v___x_3053_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_3052_, v_a_3039_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3253_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3253_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3253_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3051_);
v___x_3062_ = l_Lean_Syntax_isOfKind(v_a_3051_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
lean_dec(v_a_3051_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v___x_3063_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = l_Lean_Syntax_getArg(v_a_3051_, v___x_3064_);
lean_dec(v_a_3051_);
v___x_3066_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3065_);
v___x_3067_ = l_Lean_Syntax_isOfKind(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3065_);
v___x_3069_ = l_Lean_Syntax_isOfKind(v___x_3065_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3065_);
v___x_3071_ = l_Lean_Syntax_isOfKind(v___x_3065_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
lean_dec(v___x_3065_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v___x_3072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; lean_object* v_id_3074_; lean_object* v_binders_3075_; lean_object* v_type_3076_; lean_object* v_value_3077_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v_id_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; uint8_t v___x_3151_; 
v___x_3073_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3065_);
lean_dec(v___x_3065_);
v_id_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_id_3074_);
v_binders_3075_ = lean_ctor_get(v___x_3073_, 1);
lean_inc_ref(v_binders_3075_);
v_type_3076_ = lean_ctor_get(v___x_3073_, 2);
lean_inc(v_type_3076_);
v_value_3077_ = lean_ctor_get(v___x_3073_, 3);
lean_inc(v_value_3077_);
lean_dec_ref(v___x_3073_);
v___x_3151_ = l_Lean_Syntax_isIdent(v_id_3074_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3074_, v___x_3062_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
lean_dec(v_id_3074_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
v_id_3141_ = v_a_3153_;
v___y_3142_ = v_a_3039_;
v___y_3143_ = v_a_3040_;
v___y_3144_ = v_a_3041_;
v___y_3145_ = v_a_3042_;
v___y_3146_ = v_a_3043_;
v___y_3147_ = v_a_3044_;
v___y_3148_ = v_a_3045_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_value_3077_);
lean_dec(v_type_3076_);
lean_dec_ref(v_binders_3075_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v_a_3154_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3152_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3152_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
v_id_3141_ = v_id_3074_;
v___y_3142_ = v_a_3039_;
v___y_3143_ = v_a_3040_;
v___y_3144_ = v_a_3041_;
v___y_3145_ = v_a_3042_;
v___y_3146_ = v_a_3043_;
v___y_3147_ = v_a_3044_;
v___y_3148_ = v_a_3045_;
goto v___jp_3140_;
}
v___jp_3078_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; 
v___x_3089_ = lean_box(v___x_3062_);
v___x_3090_ = lean_box(v___x_3067_);
v___x_3091_ = lean_box(v___y_3088_);
v___f_3092_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3092_, 0, v_type_3076_);
lean_closure_set(v___f_3092_, 1, v_value_3077_);
lean_closure_set(v___f_3092_, 2, v___x_3089_);
lean_closure_set(v___f_3092_, 3, v___x_3090_);
lean_closure_set(v___f_3092_, 4, v___x_3064_);
lean_closure_set(v___f_3092_, 5, v___x_3091_);
v___x_3093_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3075_, v___f_3092_, v___y_3080_, v___y_3086_, v___y_3084_, v___y_3087_, v___y_3085_, v___y_3082_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_options_3095_; lean_object* v_fst_3096_; lean_object* v_snd_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3131_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref(v___x_3093_);
v_options_3095_ = lean_ctor_get(v___y_3085_, 2);
v_fst_3096_ = lean_ctor_get(v_a_3094_, 0);
v_snd_3097_ = lean_ctor_get(v_a_3094_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3099_ = v_a_3094_;
v_isShared_3100_ = v_isSharedCheck_3131_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_snd_3097_);
lean_inc(v_fst_3096_);
lean_dec(v_a_3094_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3131_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_inheritedTraceOptions_3101_; uint8_t v_hasTrace_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v_inheritedTraceOptions_3101_ = lean_ctor_get(v___y_3085_, 13);
v_hasTrace_3102_ = lean_ctor_get_uint8(v_options_3095_, sizeof(void*)*1);
v___x_3103_ = l_Lean_Syntax_getId(v___y_3079_);
lean_dec(v___y_3079_);
v___x_3104_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3103_);
if (v_hasTrace_3102_ == 0)
{
lean_object* v___x_3105_; 
lean_del_object(v___x_3099_);
v___x_3105_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3103_, v_fst_3096_, v_snd_3097_, v___y_3083_, v___y_3088_, v___x_3104_, v___y_3081_, v___y_3080_, v___y_3086_, v___y_3084_, v___y_3087_, v___y_3085_, v___y_3082_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3107_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3101_, v_options_3095_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_del_object(v___x_3099_);
v___x_3109_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3103_, v_fst_3096_, v_snd_3097_, v___y_3083_, v___y_3088_, v___x_3104_, v___y_3081_, v___y_3080_, v___y_3086_, v___y_3084_, v___y_3087_, v___y_3085_, v___y_3082_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_inc(v___x_3103_);
v___x_3110_ = l_Lean_MessageData_ofName(v___x_3103_);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 7);
lean_ctor_set(v___x_3099_, 1, v___x_3111_);
lean_ctor_set(v___x_3099_, 0, v___x_3110_);
v___x_3113_ = v___x_3099_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_inc(v_fst_3096_);
v___x_3114_ = l_Lean_MessageData_ofExpr(v_fst_3096_);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
lean_inc(v_snd_3097_);
v___x_3118_ = l_Lean_MessageData_ofExpr(v_snd_3097_);
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3117_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3106_, v___x_3119_, v___y_3084_, v___y_3087_, v___y_3085_, v___y_3082_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v___x_3121_; 
lean_dec_ref(v___x_3120_);
v___x_3121_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3103_, v_fst_3096_, v_snd_3097_, v___y_3083_, v___y_3088_, v___x_3104_, v___y_3081_, v___y_3080_, v___y_3086_, v___y_3084_, v___y_3087_, v___y_3085_, v___y_3082_);
return v___x_3121_;
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v___x_3103_);
lean_dec(v_snd_3097_);
lean_dec(v_fst_3096_);
lean_dec_ref(v___y_3083_);
v_a_3122_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3120_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3120_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
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
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3079_);
v_a_3132_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3093_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3093_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3149_; lean_object* v___f_3150_; 
v___x_3149_ = lean_box(v___x_3067_);
lean_inc(v_letOrReassign_3036_);
lean_inc(v_id_3141_);
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 14, 5);
lean_closure_set(v___f_3150_, 0, v_id_3141_);
lean_closure_set(v___f_3150_, 1, v_dec_3038_);
lean_closure_set(v___f_3150_, 2, v___x_3149_);
lean_closure_set(v___f_3150_, 3, v_letOrReassign_3036_);
lean_closure_set(v___f_3150_, 4, v_a_3048_);
if (lean_obj_tag(v_letOrReassign_3036_) == 1)
{
v___y_3079_ = v_id_3141_;
v___y_3080_ = v___y_3143_;
v___y_3081_ = v___y_3142_;
v___y_3082_ = v___y_3148_;
v___y_3083_ = v___f_3150_;
v___y_3084_ = v___y_3145_;
v___y_3085_ = v___y_3147_;
v___y_3086_ = v___y_3144_;
v___y_3087_ = v___y_3146_;
v___y_3088_ = v___x_3062_;
goto v___jp_3078_;
}
else
{
lean_dec(v_letOrReassign_3036_);
v___y_3079_ = v_id_3141_;
v___y_3080_ = v___y_3143_;
v___y_3081_ = v___y_3142_;
v___y_3082_ = v___y_3148_;
v___y_3083_ = v___f_3150_;
v___y_3084_ = v___y_3145_;
v___y_3085_ = v___y_3147_;
v___y_3086_ = v___y_3144_;
v___y_3087_ = v___y_3146_;
v___y_3088_ = v___x_3067_;
goto v___jp_3078_;
}
}
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = l_Lean_Syntax_getArg(v___x_3065_, v___x_3162_);
v___x_3164_ = l_Lean_Syntax_matchesNull(v___x_3163_, v___x_3064_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_dec(v___x_3065_);
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v___x_3165_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; lean_object* v_rhs_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v_xType_x3f_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3166_ = l_Lean_Syntax_getArg(v___x_3065_, v___x_3064_);
v___x_3221_ = lean_unsigned_to_nat(2u);
v___x_3222_ = l_Lean_Syntax_getArg(v___x_3065_, v___x_3221_);
v___x_3223_ = l_Lean_Syntax_isNone(v___x_3222_);
if (v___x_3223_ == 0)
{
uint8_t v___x_3224_; 
lean_inc(v___x_3222_);
v___x_3224_ = l_Lean_Syntax_matchesNull(v___x_3222_, v___x_3162_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_dec(v___x_3222_);
lean_dec(v___x_3166_);
lean_dec(v___x_3065_);
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v___x_3225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = l_Lean_Syntax_getArg(v___x_3222_, v___x_3064_);
lean_dec(v___x_3222_);
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3226_);
v___x_3228_ = l_Lean_Syntax_isOfKind(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_dec(v___x_3226_);
lean_dec(v___x_3166_);
lean_dec(v___x_3065_);
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v___x_3229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_Syntax_getArg(v___x_3226_, v___x_3162_);
lean_dec(v___x_3226_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3230_);
v___x_3232_ = v___x_3056_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
v_xType_x3f_3187_ = v___x_3232_;
v___y_3188_ = v_a_3039_;
v___y_3189_ = v_a_3040_;
v___y_3190_ = v_a_3041_;
v___y_3191_ = v_a_3042_;
v___y_3192_ = v_a_3043_;
v___y_3193_ = v_a_3044_;
v___y_3194_ = v_a_3045_;
goto v___jp_3186_;
}
}
}
}
else
{
lean_object* v___x_3234_; 
lean_dec(v___x_3222_);
lean_del_object(v___x_3056_);
v___x_3234_ = lean_box(0);
v_xType_x3f_3187_ = v___x_3234_;
v___y_3188_ = v_a_3039_;
v___y_3189_ = v_a_3040_;
v___y_3190_ = v_a_3041_;
v___y_3191_ = v_a_3042_;
v___y_3192_ = v_a_3043_;
v___y_3193_ = v_a_3044_;
v___y_3194_ = v_a_3045_;
goto v___jp_3186_;
}
v___jp_3167_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3176_ = lean_box(v___x_3067_);
v___x_3177_ = lean_box(v___x_3062_);
lean_inc(v___x_3166_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 17, 8);
lean_closure_set(v___f_3178_, 0, v_a_3054_);
lean_closure_set(v___f_3178_, 1, v_rhs_3168_);
lean_closure_set(v___f_3178_, 2, v___x_3176_);
lean_closure_set(v___f_3178_, 3, v___x_3058_);
lean_closure_set(v___f_3178_, 4, v___x_3059_);
lean_closure_set(v___f_3178_, 5, v___x_3060_);
lean_closure_set(v___f_3178_, 6, v___x_3166_);
lean_closure_set(v___f_3178_, 7, v___x_3177_);
v___x_3179_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3179_, 0, v_dec_3038_);
v___x_3180_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3180_, 0, v_letOrReassign_3036_);
lean_closure_set(v___x_3180_, 1, v_a_3048_);
lean_closure_set(v___x_3180_, 2, v___x_3179_);
v___x_3181_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3182_ = l_Lean_MessageData_ofSyntax(v___x_3166_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_box(0);
v___x_3185_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3183_, v___x_3180_, v___f_3178_, v___x_3184_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3185_;
}
v___jp_3186_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_unsigned_to_nat(4u);
v___x_3196_ = l_Lean_Syntax_getArg(v___x_3065_, v___x_3195_);
lean_dec(v___x_3065_);
if (lean_obj_tag(v_xType_x3f_3187_) == 0)
{
v_rhs_3168_ = v___x_3196_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3192_;
v___y_3174_ = v___y_3193_;
v___y_3175_ = v___y_3194_;
goto v___jp_3167_;
}
else
{
lean_object* v_val_3197_; lean_object* v_ref_3198_; lean_object* v_quotContext_3199_; lean_object* v_currMacroScope_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_val_3197_ = lean_ctor_get(v_xType_x3f_3187_, 0);
lean_inc(v_val_3197_);
lean_dec_ref(v_xType_x3f_3187_);
v_ref_3198_ = lean_ctor_get(v___y_3193_, 5);
v_quotContext_3199_ = lean_ctor_get(v___y_3193_, 10);
v_currMacroScope_3200_ = lean_ctor_get(v___y_3193_, 11);
v___x_3201_ = l_Lean_SourceInfo_fromRef(v_ref_3198_, v___x_3067_);
v___x_3202_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3203_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3204_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3201_, 7);
v___x_3205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3201_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3207_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3208_ = lean_box(0);
lean_inc(v_currMacroScope_3200_);
lean_inc(v_quotContext_3199_);
v___x_3209_ = l_Lean_addMacroScope(v_quotContext_3199_, v___x_3208_, v_currMacroScope_3200_);
v___x_3210_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3201_);
lean_ctor_set(v___x_3211_, 1, v___x_3207_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_node1(v___x_3201_, v___x_3206_, v___x_3211_);
v___x_3213_ = l_Lean_Syntax_node2(v___x_3201_, v___x_3203_, v___x_3205_, v___x_3212_);
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3201_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3217_ = l_Lean_Syntax_node1(v___x_3201_, v___x_3216_, v_val_3197_);
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3201_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = l_Lean_Syntax_node5(v___x_3201_, v___x_3202_, v___x_3213_, v___x_3196_, v___x_3215_, v___x_3217_, v___x_3219_);
v_rhs_3168_ = v___x_3220_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3192_;
v___y_3174_ = v___y_3193_;
v___y_3175_ = v___y_3194_;
goto v___jp_3167_;
}
}
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_del_object(v___x_3056_);
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
v___x_3235_ = lean_box(v___x_3062_);
lean_inc(v___x_3065_);
v___x_3236_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3236_, 0, v___x_3065_);
lean_closure_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3236_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v_ref_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3237_);
v_ref_3239_ = lean_ctor_get(v_a_3044_, 5);
v___x_3240_ = 0;
v___x_3241_ = l_Lean_SourceInfo_fromRef(v_ref_3239_, v___x_3240_);
v___x_3242_ = l_Lean_Syntax_node1(v___x_3241_, v___x_3061_, v_a_3238_);
lean_inc(v___x_3242_);
v___x_3243_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 11, 3);
lean_closure_set(v___x_3243_, 0, v_letOrReassign_3036_);
lean_closure_set(v___x_3243_, 1, v___x_3242_);
lean_closure_set(v___x_3243_, 2, v_dec_3038_);
v___x_3244_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3065_, v___x_3242_, v___x_3243_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3244_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v___x_3065_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v_a_3245_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3237_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3237_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3051_);
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
return v___x_3053_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_letOrReassign_3036_);
v_a_3254_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3050_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3050_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_a_3048_);
lean_dec_ref(v_dec_3038_);
lean_dec(v_decl_3037_);
lean_dec(v_letOrReassign_3036_);
v_a_3262_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3049_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3049_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_dec_3038_);
lean_dec(v_decl_3037_);
lean_dec(v_letOrReassign_3036_);
v_a_3270_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3047_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3047_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3279_, v_x_3280_, v_x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3283_, lean_object* v_msg_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3283_, v_msg_3284_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3294_, lean_object* v_msg_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3294_, v_msg_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3310_, v___y_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3323_, lean_object* v_beforeStx_3324_, lean_object* v_afterStx_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3324_, v_afterStx_3325_, v_x_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_beforeStx_3337_, lean_object* v_afterStx_3338_, lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3336_, v_beforeStx_3337_, v_afterStx_3338_, v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3350_, v___y_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3354_, v_x_3355_, v___y_3356_, v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec_ref(v_x_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3359_, lean_object* v_ref_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3360_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3370_, lean_object* v_ref_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3370_, v_ref_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec_ref(v___y_3372_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3392_, v_x_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3403_, lean_object* v_x_3404_, size_t v_x_3405_, size_t v_x_3406_, lean_object* v_x_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3404_, v_x_3405_, v_x_3406_, v_x_3407_, v_x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3410_, lean_object* v_x_3411_, lean_object* v_x_3412_, lean_object* v_x_3413_, lean_object* v_x_3414_, lean_object* v_x_3415_){
_start:
{
size_t v_x_80137__boxed_3416_; size_t v_x_80138__boxed_3417_; lean_object* v_res_3418_; 
v_x_80137__boxed_3416_ = lean_unbox_usize(v_x_3412_);
lean_dec(v_x_3412_);
v_x_80138__boxed_3417_ = lean_unbox_usize(v_x_3413_);
lean_dec(v_x_3413_);
v_res_3418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3410_, v_x_3411_, v_x_80137__boxed_3416_, v_x_80138__boxed_3417_, v_x_3414_, v_x_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3419_, lean_object* v_stx_3420_, lean_object* v_output_3421_, lean_object* v_x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3420_, v_output_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3431_, lean_object* v_stx_3432_, lean_object* v_output_3433_, lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3431_, v_stx_3432_, v_output_3433_, v_x_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3443_, lean_object* v_as_x27_3444_, lean_object* v_b_3445_, lean_object* v_a_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3444_, v_b_3445_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3456_, lean_object* v_as_x27_3457_, lean_object* v_b_3458_, lean_object* v_a_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3456_, v_as_x27_3457_, v_b_3458_, v_a_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v_as_3456_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3469_, lean_object* v_ref_3470_, lean_object* v_msg_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3470_, v_msg_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_ref_3482_, lean_object* v_msg_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3481_, v_ref_3482_, v_msg_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v_ref_3482_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3493_, lean_object* v_n_3494_, lean_object* v_k_3495_, lean_object* v_v_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3494_, v_k_3495_, v_v_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3498_, size_t v_depth_3499_, lean_object* v_keys_3500_, lean_object* v_vals_3501_, lean_object* v_heq_3502_, lean_object* v_i_3503_, lean_object* v_entries_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3499_, v_keys_3500_, v_vals_3501_, v_i_3503_, v_entries_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3506_, lean_object* v_depth_3507_, lean_object* v_keys_3508_, lean_object* v_vals_3509_, lean_object* v_heq_3510_, lean_object* v_i_3511_, lean_object* v_entries_3512_){
_start:
{
size_t v_depth_boxed_3513_; lean_object* v_res_3514_; 
v_depth_boxed_3513_ = lean_unbox_usize(v_depth_3507_);
lean_dec(v_depth_3507_);
v_res_3514_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3506_, v_depth_boxed_3513_, v_keys_3508_, v_vals_3509_, v_heq_3510_, v_i_3511_, v_entries_3512_);
lean_dec_ref(v_vals_3509_);
lean_dec_ref(v_keys_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3531_, lean_object* v_x_3532_, lean_object* v_mkInfoTree_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3532_, v_mkInfoTree_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_x_3543_, lean_object* v_mkInfoTree_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3542_, v_x_3543_, v_mkInfoTree_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22(lean_object* v_00_u03b1_3553_, lean_object* v_msg_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(v_msg_3554_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___boxed(lean_object* v_00_u03b1_3564_, lean_object* v_msg_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22(v_00_u03b1_3564_, v_msg_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_, lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3576_, v_x_3577_, v_x_3578_, v_x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
uint8_t v___x_3584_; 
v___x_3584_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3582_, v_x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
uint8_t v_res_3588_; lean_object* v_r_3589_; 
v_res_3588_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3585_, v_x_3586_, v_x_3587_);
lean_dec_ref(v_x_3587_);
lean_dec_ref(v_x_3586_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3590_, lean_object* v_x_3591_, size_t v_x_3592_, lean_object* v_x_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3591_, v_x_3592_, v_x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
size_t v_x_80326__boxed_3599_; uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_x_80326__boxed_3599_ = lean_unbox_usize(v_x_3597_);
lean_dec(v_x_3597_);
v_res_3600_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3595_, v_x_3596_, v_x_80326__boxed_3599_, v_x_3598_);
lean_dec_ref(v_x_3598_);
lean_dec_ref(v_x_3596_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3602_, lean_object* v_keys_3603_, lean_object* v_vals_3604_, lean_object* v_heq_3605_, lean_object* v_i_3606_, lean_object* v_k_3607_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3603_, v_i_3606_, v_k_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3609_, lean_object* v_keys_3610_, lean_object* v_vals_3611_, lean_object* v_heq_3612_, lean_object* v_i_3613_, lean_object* v_k_3614_){
_start:
{
uint8_t v_res_3615_; lean_object* v_r_3616_; 
v_res_3615_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3609_, v_keys_3610_, v_vals_3611_, v_heq_3612_, v_i_3613_, v_k_3614_);
lean_dec_ref(v_k_3614_);
lean_dec_ref(v_vals_3611_);
lean_dec_ref(v_keys_3610_);
v_r_3616_ = lean_box(v_res_3615_);
return v_r_3616_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3626_, lean_object* v_otherwise_x3f_3627_, uint8_t v___x_3628_, lean_object* v___x_3629_, lean_object* v___x_3630_, lean_object* v___x_3631_, lean_object* v___x_3632_, lean_object* v___x_3633_, lean_object* v_dec_3634_, uint8_t v___x_3635_, lean_object* v___y_3636_, lean_object* v___x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___y_3669_; 
switch(lean_obj_tag(v_letOrReassign_3626_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3627_) == 1)
{
lean_object* v_mutTk_x3f_3680_; lean_object* v_val_3681_; lean_object* v_ref_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3712_; 
v_mutTk_x3f_3680_ = lean_ctor_get(v_letOrReassign_3626_, 0);
v_val_3681_ = lean_ctor_get(v_otherwise_x3f_3627_, 0);
lean_inc(v_val_3681_);
lean_dec_ref(v_otherwise_x3f_3627_);
v_ref_3682_ = lean_ctor_get(v___y_3643_, 5);
v___x_3683_ = l_Lean_SourceInfo_fromRef(v_ref_3682_, v___x_3628_);
v___x_3684_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3631_);
lean_inc_ref(v___x_3630_);
lean_inc_ref(v___x_3629_);
v___x_3685_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3684_);
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3683_);
v___x_3687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3683_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3689_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3680_) == 1)
{
lean_object* v_val_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_val_3727_ = lean_ctor_get(v_mutTk_x3f_3680_, 0);
v___x_3728_ = l_Lean_SourceInfo_fromRef(v_val_3727_, v___x_3635_);
v___x_3729_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l_Array_mkArray1___redArg(v___x_3730_);
v___y_3712_ = v___x_3731_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___y_3712_ = v___x_3732_;
goto v___jp_3711_;
}
v___jp_3690_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3696_ = l_Array_append___redArg(v___x_3689_, v___y_3695_);
lean_dec_ref(v___y_3695_);
lean_inc(v___x_3683_);
v___x_3697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3683_);
lean_ctor_set(v___x_3697_, 1, v___x_3688_);
lean_ctor_set(v___x_3697_, 2, v___x_3696_);
v___x_3698_ = lean_unsigned_to_nat(9u);
v___x_3699_ = lean_mk_empty_array_with_capacity(v___x_3698_);
v___x_3700_ = lean_array_push(v___x_3699_, v___x_3687_);
v___x_3701_ = lean_array_push(v___x_3700_, v___y_3693_);
v___x_3702_ = lean_array_push(v___x_3701_, v___y_3691_);
v___x_3703_ = lean_array_push(v___x_3702_, v___x_3632_);
v___x_3704_ = lean_array_push(v___x_3703_, v___y_3692_);
v___x_3705_ = lean_array_push(v___x_3704_, v___x_3633_);
v___x_3706_ = lean_array_push(v___x_3705_, v___y_3694_);
v___x_3707_ = lean_array_push(v___x_3706_, v_val_3681_);
v___x_3708_ = lean_array_push(v___x_3707_, v___x_3697_);
v___x_3709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3683_);
lean_ctor_set(v___x_3709_, 1, v___x_3685_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = l_Lean_Elab_Do_elabDoElem(v___x_3709_, v_dec_3634_, v___x_3635_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3710_;
}
v___jp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3713_ = l_Array_append___redArg(v___x_3689_, v___y_3712_);
lean_dec_ref(v___y_3712_);
lean_inc_n(v___x_3683_, 5);
v___x_3714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3683_);
lean_ctor_set(v___x_3714_, 1, v___x_3688_);
lean_ctor_set(v___x_3714_, 2, v___x_3713_);
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3716_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3683_);
lean_ctor_set(v___x_3717_, 1, v___x_3688_);
lean_ctor_set(v___x_3717_, 2, v___x_3689_);
v___x_3718_ = l_Lean_Syntax_node1(v___x_3683_, v___x_3716_, v___x_3717_);
v___x_3719_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3683_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
v___x_3722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3683_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
if (lean_obj_tag(v___y_3636_) == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___y_3691_ = v___x_3718_;
v___y_3692_ = v___x_3720_;
v___y_3693_ = v___x_3714_;
v___y_3694_ = v___x_3722_;
v___y_3695_ = v___x_3723_;
goto v___jp_3690_;
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_val_3724_ = lean_ctor_get(v___y_3636_, 0);
lean_inc(v_val_3724_);
lean_dec_ref(v___y_3636_);
v___x_3725_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___x_3726_ = lean_array_push(v___x_3725_, v_val_3724_);
v___y_3691_ = v___x_3718_;
v___y_3692_ = v___x_3720_;
v___y_3693_ = v___x_3714_;
v___y_3694_ = v___x_3722_;
v___y_3695_ = v___x_3726_;
goto v___jp_3690_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3733_; lean_object* v_ref_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___y_3743_; 
lean_dec(v___y_3636_);
lean_dec(v_otherwise_x3f_3627_);
v_mutTk_x3f_3733_ = lean_ctor_get(v_letOrReassign_3626_, 0);
v_ref_3734_ = lean_ctor_get(v___y_3643_, 5);
v___x_3735_ = l_Lean_SourceInfo_fromRef(v_ref_3734_, v___x_3628_);
v___x_3736_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3631_);
lean_inc_ref(v___x_3630_);
lean_inc_ref(v___x_3629_);
v___x_3737_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3735_);
v___x_3739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3735_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3741_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3733_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_val_3760_ = lean_ctor_get(v_mutTk_x3f_3733_, 0);
v___x_3761_ = l_Lean_SourceInfo_fromRef(v_val_3760_, v___x_3635_);
v___x_3762_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = l_Array_mkArray1___redArg(v___x_3763_);
v___y_3743_ = v___x_3764_;
goto v___jp_3742_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___y_3743_ = v___x_3765_;
goto v___jp_3742_;
}
v___jp_3742_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3744_ = l_Array_append___redArg(v___x_3741_, v___y_3743_);
lean_dec_ref(v___y_3743_);
lean_inc_n(v___x_3735_, 6);
v___x_3745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3735_);
lean_ctor_set(v___x_3745_, 1, v___x_3740_);
lean_ctor_set(v___x_3745_, 2, v___x_3744_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3631_, 2);
lean_inc_ref_n(v___x_3630_, 2);
lean_inc_ref_n(v___x_3629_, 2);
v___x_3747_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3735_);
lean_ctor_set(v___x_3748_, 1, v___x_3740_);
lean_ctor_set(v___x_3748_, 2, v___x_3741_);
lean_inc_ref_n(v___x_3748_, 2);
v___x_3749_ = l_Lean_Syntax_node1(v___x_3735_, v___x_3747_, v___x_3748_);
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3751_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3750_);
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3753_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3752_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3735_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = l_Lean_Syntax_node5(v___x_3735_, v___x_3753_, v___x_3632_, v___x_3748_, v___x_3748_, v___x_3755_, v___x_3633_);
v___x_3757_ = l_Lean_Syntax_node1(v___x_3735_, v___x_3751_, v___x_3756_);
v___x_3758_ = l_Lean_Syntax_node4(v___x_3735_, v___x_3737_, v___x_3739_, v___x_3745_, v___x_3749_, v___x_3757_);
v___x_3759_ = l_Lean_Elab_Do_elabDoElem(v___x_3758_, v_dec_3634_, v___x_3635_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3759_;
}
}
}
case 1:
{
lean_dec(v___y_3636_);
if (lean_obj_tag(v_otherwise_x3f_3627_) == 1)
{
lean_object* v___x_3766_; 
lean_dec_ref(v_otherwise_x3f_3627_);
lean_dec_ref(v_dec_3634_);
lean_dec(v___x_3633_);
lean_dec(v___x_3632_);
lean_dec_ref(v___x_3631_);
lean_dec_ref(v___x_3630_);
lean_dec_ref(v___x_3629_);
v___x_3766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3766_;
}
else
{
lean_object* v_ref_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec(v_otherwise_x3f_3627_);
v_ref_3767_ = lean_ctor_get(v___y_3643_, 5);
v___x_3768_ = l_Lean_SourceInfo_fromRef(v_ref_3767_, v___x_3628_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3631_, 3);
lean_inc_ref_n(v___x_3630_, 3);
lean_inc_ref_n(v___x_3629_, 3);
v___x_3770_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3768_, 6);
v___x_3772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3768_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3774_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3773_);
v___x_3775_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3776_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3768_);
lean_ctor_set(v___x_3777_, 1, v___x_3775_);
lean_ctor_set(v___x_3777_, 2, v___x_3776_);
lean_inc_ref_n(v___x_3777_, 2);
v___x_3778_ = l_Lean_Syntax_node1(v___x_3768_, v___x_3774_, v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3780_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3782_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3781_);
v___x_3783_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3768_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = l_Lean_Syntax_node5(v___x_3768_, v___x_3782_, v___x_3632_, v___x_3777_, v___x_3777_, v___x_3784_, v___x_3633_);
v___x_3786_ = l_Lean_Syntax_node1(v___x_3768_, v___x_3780_, v___x_3785_);
v___x_3787_ = l_Lean_Syntax_node3(v___x_3768_, v___x_3770_, v___x_3772_, v___x_3778_, v___x_3786_);
v___x_3788_ = l_Lean_Elab_Do_elabDoElem(v___x_3787_, v_dec_3634_, v___x_3635_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3788_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3627_);
if (lean_obj_tag(v___y_3636_) == 0)
{
v___y_3669_ = v___x_3635_;
goto v___jp_3668_;
}
else
{
lean_dec_ref(v___y_3636_);
v___y_3669_ = v___x_3628_;
goto v___jp_3668_;
}
}
}
v___jp_3646_:
{
lean_object* v_ref_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_ref_3654_ = lean_ctor_get(v___y_3652_, 5);
v___x_3655_ = l_Lean_SourceInfo_fromRef(v_ref_3654_, v___x_3628_);
v___x_3656_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3631_);
lean_inc_ref(v___x_3630_);
lean_inc_ref(v___x_3629_);
v___x_3657_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3656_);
v___x_3658_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3659_ = l_Lean_Name_mkStr4(v___x_3629_, v___x_3630_, v___x_3631_, v___x_3658_);
v___x_3660_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3661_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3655_, 3);
v___x_3662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3655_);
lean_ctor_set(v___x_3662_, 1, v___x_3660_);
lean_ctor_set(v___x_3662_, 2, v___x_3661_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3655_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
lean_inc_ref(v___x_3662_);
v___x_3665_ = l_Lean_Syntax_node5(v___x_3655_, v___x_3659_, v___x_3632_, v___x_3662_, v___x_3662_, v___x_3664_, v___x_3633_);
v___x_3666_ = l_Lean_Syntax_node1(v___x_3655_, v___x_3657_, v___x_3665_);
v___x_3667_ = l_Lean_Elab_Do_elabDoElem(v___x_3666_, v_dec_3634_, v___x_3635_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3667_;
}
v___jp_3668_:
{
if (v___y_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v_dec_3634_);
lean_dec(v___x_3633_);
lean_dec(v___x_3632_);
lean_dec_ref(v___x_3631_);
lean_dec_ref(v___x_3630_);
lean_dec_ref(v___x_3629_);
v___x_3670_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3671_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(v___x_3670_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
v___y_3647_ = v___y_3638_;
v___y_3648_ = v___y_3639_;
v___y_3649_ = v___y_3640_;
v___y_3650_ = v___y_3641_;
v___y_3651_ = v___y_3642_;
v___y_3652_ = v___y_3643_;
v___y_3653_ = v___y_3644_;
goto v___jp_3646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_3789_ = _args[0];
lean_object* v_otherwise_x3f_3790_ = _args[1];
lean_object* v___x_3791_ = _args[2];
lean_object* v___x_3792_ = _args[3];
lean_object* v___x_3793_ = _args[4];
lean_object* v___x_3794_ = _args[5];
lean_object* v___x_3795_ = _args[6];
lean_object* v___x_3796_ = _args[7];
lean_object* v_dec_3797_ = _args[8];
lean_object* v___x_3798_ = _args[9];
lean_object* v___y_3799_ = _args[10];
lean_object* v___x_3800_ = _args[11];
lean_object* v___y_3801_ = _args[12];
lean_object* v___y_3802_ = _args[13];
lean_object* v___y_3803_ = _args[14];
lean_object* v___y_3804_ = _args[15];
lean_object* v___y_3805_ = _args[16];
lean_object* v___y_3806_ = _args[17];
lean_object* v___y_3807_ = _args[18];
lean_object* v___y_3808_ = _args[19];
_start:
{
uint8_t v___x_38464__boxed_3809_; uint8_t v___x_38470__boxed_3810_; lean_object* v_res_3811_; 
v___x_38464__boxed_3809_ = lean_unbox(v___x_3791_);
v___x_38470__boxed_3810_ = lean_unbox(v___x_3798_);
v_res_3811_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_3789_, v_otherwise_x3f_3790_, v___x_38464__boxed_3809_, v___x_3792_, v___x_3793_, v___x_3794_, v___x_3795_, v___x_3796_, v_dec_3797_, v___x_38470__boxed_3810_, v___y_3799_, v___x_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___x_3800_);
lean_dec(v_letOrReassign_3789_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_3812_, lean_object* v_otherwise_x3f_3813_, uint8_t v___x_3814_, lean_object* v___x_3815_, lean_object* v___x_3816_, lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v_dec_3820_, uint8_t v___x_3821_, lean_object* v___y_3822_, lean_object* v___x_3823_, uint8_t v___x_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; uint8_t v___y_3856_; 
switch(lean_obj_tag(v_letOrReassign_3812_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3813_) == 1)
{
lean_object* v_mutTk_x3f_3867_; lean_object* v_val_3868_; lean_object* v_ref_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3899_; 
v_mutTk_x3f_3867_ = lean_ctor_get(v_letOrReassign_3812_, 0);
v_val_3868_ = lean_ctor_get(v_otherwise_x3f_3813_, 0);
lean_inc(v_val_3868_);
lean_dec_ref(v_otherwise_x3f_3813_);
v_ref_3869_ = lean_ctor_get(v___y_3830_, 5);
v___x_3870_ = l_Lean_SourceInfo_fromRef(v_ref_3869_, v___x_3814_);
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3817_);
lean_inc_ref(v___x_3816_);
lean_inc_ref(v___x_3815_);
v___x_3872_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3871_);
v___x_3873_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3870_);
v___x_3874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3870_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3876_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3867_) == 1)
{
lean_object* v_val_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_val_3914_ = lean_ctor_get(v_mutTk_x3f_3867_, 0);
v___x_3915_ = l_Lean_SourceInfo_fromRef(v_val_3914_, v___x_3821_);
v___x_3916_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = l_Array_mkArray1___redArg(v___x_3917_);
v___y_3899_ = v___x_3918_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___y_3899_ = v___x_3919_;
goto v___jp_3898_;
}
v___jp_3877_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3883_ = l_Array_append___redArg(v___x_3876_, v___y_3882_);
lean_dec_ref(v___y_3882_);
lean_inc(v___x_3870_);
v___x_3884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3870_);
lean_ctor_set(v___x_3884_, 1, v___x_3875_);
lean_ctor_set(v___x_3884_, 2, v___x_3883_);
v___x_3885_ = lean_unsigned_to_nat(9u);
v___x_3886_ = lean_mk_empty_array_with_capacity(v___x_3885_);
v___x_3887_ = lean_array_push(v___x_3886_, v___x_3874_);
v___x_3888_ = lean_array_push(v___x_3887_, v___y_3878_);
v___x_3889_ = lean_array_push(v___x_3888_, v___y_3879_);
v___x_3890_ = lean_array_push(v___x_3889_, v___x_3818_);
v___x_3891_ = lean_array_push(v___x_3890_, v___y_3880_);
v___x_3892_ = lean_array_push(v___x_3891_, v___x_3819_);
v___x_3893_ = lean_array_push(v___x_3892_, v___y_3881_);
v___x_3894_ = lean_array_push(v___x_3893_, v_val_3868_);
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3884_);
v___x_3896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3870_);
lean_ctor_set(v___x_3896_, 1, v___x_3872_);
lean_ctor_set(v___x_3896_, 2, v___x_3895_);
v___x_3897_ = l_Lean_Elab_Do_elabDoElem(v___x_3896_, v_dec_3820_, v___x_3821_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3897_;
}
v___jp_3898_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3900_ = l_Array_append___redArg(v___x_3876_, v___y_3899_);
lean_dec_ref(v___y_3899_);
lean_inc_n(v___x_3870_, 5);
v___x_3901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3870_);
lean_ctor_set(v___x_3901_, 1, v___x_3875_);
lean_ctor_set(v___x_3901_, 2, v___x_3900_);
v___x_3902_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3903_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3902_);
v___x_3904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3870_);
lean_ctor_set(v___x_3904_, 1, v___x_3875_);
lean_ctor_set(v___x_3904_, 2, v___x_3876_);
v___x_3905_ = l_Lean_Syntax_node1(v___x_3870_, v___x_3903_, v___x_3904_);
v___x_3906_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3870_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
v___x_3909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3870_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
if (lean_obj_tag(v___y_3822_) == 0)
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___y_3878_ = v___x_3901_;
v___y_3879_ = v___x_3905_;
v___y_3880_ = v___x_3907_;
v___y_3881_ = v___x_3909_;
v___y_3882_ = v___x_3910_;
goto v___jp_3877_;
}
else
{
lean_object* v_val_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_val_3911_ = lean_ctor_get(v___y_3822_, 0);
lean_inc(v_val_3911_);
lean_dec_ref(v___y_3822_);
v___x_3912_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___x_3913_ = lean_array_push(v___x_3912_, v_val_3911_);
v___y_3878_ = v___x_3901_;
v___y_3879_ = v___x_3905_;
v___y_3880_ = v___x_3907_;
v___y_3881_ = v___x_3909_;
v___y_3882_ = v___x_3913_;
goto v___jp_3877_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3920_; lean_object* v_ref_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___y_3930_; 
lean_dec(v___y_3822_);
lean_dec(v_otherwise_x3f_3813_);
v_mutTk_x3f_3920_ = lean_ctor_get(v_letOrReassign_3812_, 0);
v_ref_3921_ = lean_ctor_get(v___y_3830_, 5);
v___x_3922_ = l_Lean_SourceInfo_fromRef(v_ref_3921_, v___x_3814_);
v___x_3923_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3817_);
lean_inc_ref(v___x_3816_);
lean_inc_ref(v___x_3815_);
v___x_3924_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3923_);
v___x_3925_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3922_);
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3922_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3928_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3920_) == 1)
{
lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_val_3947_ = lean_ctor_get(v_mutTk_x3f_3920_, 0);
v___x_3948_ = l_Lean_SourceInfo_fromRef(v_val_3947_, v___x_3821_);
v___x_3949_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = l_Array_mkArray1___redArg(v___x_3950_);
v___y_3930_ = v___x_3951_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_mk_empty_array_with_capacity(v___x_3823_);
v___y_3930_ = v___x_3952_;
goto v___jp_3929_;
}
v___jp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3931_ = l_Array_append___redArg(v___x_3928_, v___y_3930_);
lean_dec_ref(v___y_3930_);
lean_inc_n(v___x_3922_, 6);
v___x_3932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3922_);
lean_ctor_set(v___x_3932_, 1, v___x_3927_);
lean_ctor_set(v___x_3932_, 2, v___x_3931_);
v___x_3933_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3817_, 2);
lean_inc_ref_n(v___x_3816_, 2);
lean_inc_ref_n(v___x_3815_, 2);
v___x_3934_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3922_);
lean_ctor_set(v___x_3935_, 1, v___x_3927_);
lean_ctor_set(v___x_3935_, 2, v___x_3928_);
lean_inc_ref_n(v___x_3935_, 2);
v___x_3936_ = l_Lean_Syntax_node1(v___x_3922_, v___x_3934_, v___x_3935_);
v___x_3937_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3938_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3937_);
v___x_3939_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3940_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3939_);
v___x_3941_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3922_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = l_Lean_Syntax_node5(v___x_3922_, v___x_3940_, v___x_3818_, v___x_3935_, v___x_3935_, v___x_3942_, v___x_3819_);
v___x_3944_ = l_Lean_Syntax_node1(v___x_3922_, v___x_3938_, v___x_3943_);
v___x_3945_ = l_Lean_Syntax_node4(v___x_3922_, v___x_3924_, v___x_3926_, v___x_3932_, v___x_3936_, v___x_3944_);
v___x_3946_ = l_Lean_Elab_Do_elabDoElem(v___x_3945_, v_dec_3820_, v___x_3821_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3946_;
}
}
}
case 1:
{
lean_dec(v___y_3822_);
if (lean_obj_tag(v_otherwise_x3f_3813_) == 1)
{
lean_object* v___x_3953_; 
lean_dec_ref(v_otherwise_x3f_3813_);
lean_dec_ref(v_dec_3820_);
lean_dec(v___x_3819_);
lean_dec(v___x_3818_);
lean_dec_ref(v___x_3817_);
lean_dec_ref(v___x_3816_);
lean_dec_ref(v___x_3815_);
v___x_3953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3953_;
}
else
{
lean_object* v_ref_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec(v_otherwise_x3f_3813_);
v_ref_3954_ = lean_ctor_get(v___y_3830_, 5);
v___x_3955_ = l_Lean_SourceInfo_fromRef(v_ref_3954_, v___x_3814_);
v___x_3956_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3817_, 3);
lean_inc_ref_n(v___x_3816_, 3);
lean_inc_ref_n(v___x_3815_, 3);
v___x_3957_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3956_);
v___x_3958_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3955_, 6);
v___x_3959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3955_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3961_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3960_);
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3963_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3955_);
lean_ctor_set(v___x_3964_, 1, v___x_3962_);
lean_ctor_set(v___x_3964_, 2, v___x_3963_);
lean_inc_ref_n(v___x_3964_, 2);
v___x_3965_ = l_Lean_Syntax_node1(v___x_3955_, v___x_3961_, v___x_3964_);
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3967_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3966_);
v___x_3968_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3969_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3968_);
v___x_3970_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3955_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = l_Lean_Syntax_node5(v___x_3955_, v___x_3969_, v___x_3818_, v___x_3964_, v___x_3964_, v___x_3971_, v___x_3819_);
v___x_3973_ = l_Lean_Syntax_node1(v___x_3955_, v___x_3967_, v___x_3972_);
v___x_3974_ = l_Lean_Syntax_node3(v___x_3955_, v___x_3957_, v___x_3959_, v___x_3965_, v___x_3973_);
v___x_3975_ = l_Lean_Elab_Do_elabDoElem(v___x_3974_, v_dec_3820_, v___x_3821_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3975_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3813_);
if (lean_obj_tag(v___y_3822_) == 0)
{
v___y_3856_ = v___x_3824_;
goto v___jp_3855_;
}
else
{
lean_dec_ref(v___y_3822_);
v___y_3856_ = v___x_3814_;
goto v___jp_3855_;
}
}
}
v___jp_3833_:
{
lean_object* v_ref_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_ref_3841_ = lean_ctor_get(v___y_3839_, 5);
v___x_3842_ = l_Lean_SourceInfo_fromRef(v_ref_3841_, v___x_3814_);
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3817_);
lean_inc_ref(v___x_3816_);
lean_inc_ref(v___x_3815_);
v___x_3844_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3843_);
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3846_ = l_Lean_Name_mkStr4(v___x_3815_, v___x_3816_, v___x_3817_, v___x_3845_);
v___x_3847_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3848_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3842_, 3);
v___x_3849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3842_);
lean_ctor_set(v___x_3849_, 1, v___x_3847_);
lean_ctor_set(v___x_3849_, 2, v___x_3848_);
v___x_3850_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3842_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
lean_inc_ref(v___x_3849_);
v___x_3852_ = l_Lean_Syntax_node5(v___x_3842_, v___x_3846_, v___x_3818_, v___x_3849_, v___x_3849_, v___x_3851_, v___x_3819_);
v___x_3853_ = l_Lean_Syntax_node1(v___x_3842_, v___x_3844_, v___x_3852_);
v___x_3854_ = l_Lean_Elab_Do_elabDoElem(v___x_3853_, v_dec_3820_, v___x_3821_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3854_;
}
v___jp_3855_:
{
if (v___y_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v_dec_3820_);
lean_dec(v___x_3819_);
lean_dec(v___x_3818_);
lean_dec_ref(v___x_3817_);
lean_dec_ref(v___x_3816_);
lean_dec_ref(v___x_3815_);
v___x_3857_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3858_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16_spec__22___redArg(v___x_3857_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
else
{
v___y_3834_ = v___y_3825_;
v___y_3835_ = v___y_3826_;
v___y_3836_ = v___y_3827_;
v___y_3837_ = v___y_3828_;
v___y_3838_ = v___y_3829_;
v___y_3839_ = v___y_3830_;
v___y_3840_ = v___y_3831_;
goto v___jp_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_3976_ = _args[0];
lean_object* v_otherwise_x3f_3977_ = _args[1];
lean_object* v___x_3978_ = _args[2];
lean_object* v___x_3979_ = _args[3];
lean_object* v___x_3980_ = _args[4];
lean_object* v___x_3981_ = _args[5];
lean_object* v___x_3982_ = _args[6];
lean_object* v___x_3983_ = _args[7];
lean_object* v_dec_3984_ = _args[8];
lean_object* v___x_3985_ = _args[9];
lean_object* v___y_3986_ = _args[10];
lean_object* v___x_3987_ = _args[11];
lean_object* v___x_3988_ = _args[12];
lean_object* v___y_3989_ = _args[13];
lean_object* v___y_3990_ = _args[14];
lean_object* v___y_3991_ = _args[15];
lean_object* v___y_3992_ = _args[16];
lean_object* v___y_3993_ = _args[17];
lean_object* v___y_3994_ = _args[18];
lean_object* v___y_3995_ = _args[19];
lean_object* v___y_3996_ = _args[20];
_start:
{
uint8_t v___x_38846__boxed_3997_; uint8_t v___x_38852__boxed_3998_; uint8_t v___x_38855__boxed_3999_; lean_object* v_res_4000_; 
v___x_38846__boxed_3997_ = lean_unbox(v___x_3978_);
v___x_38852__boxed_3998_ = lean_unbox(v___x_3985_);
v___x_38855__boxed_3999_ = lean_unbox(v___x_3988_);
v_res_4000_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_3976_, v_otherwise_x3f_3977_, v___x_38846__boxed_3997_, v___x_3979_, v___x_3980_, v___x_3981_, v___x_3982_, v___x_3983_, v_dec_3984_, v___x_38852__boxed_3998_, v___y_3986_, v___x_3987_, v___x_38855__boxed_3999_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___x_3987_);
lean_dec(v_letOrReassign_3976_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4021_, lean_object* v_stx_4022_, lean_object* v_dec_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4022_);
v___x_4036_ = l_Lean_Syntax_isOfKind(v_stx_4022_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4037_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4022_);
v___x_4038_ = l_Lean_Syntax_isOfKind(v_stx_4022_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; 
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4039_;
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4040_);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4041_);
v___x_4043_ = l_Lean_Syntax_isOfKind(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4129_; lean_object* v_patType_x3f_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v___x_4129_ = lean_unsigned_to_nat(1u);
v___x_4160_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4129_);
v___x_4161_ = l_Lean_Syntax_isNone(v___x_4160_);
if (v___x_4161_ == 0)
{
uint8_t v___x_4162_; 
lean_inc(v___x_4160_);
v___x_4162_ = l_Lean_Syntax_matchesNull(v___x_4160_, v___x_4129_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; 
lean_dec(v___x_4160_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4163_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4163_;
}
else
{
lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4164_ = l_Lean_Syntax_getArg(v___x_4160_, v___x_4040_);
lean_dec(v___x_4160_);
v___x_4165_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4164_);
v___x_4166_ = l_Lean_Syntax_isOfKind(v___x_4164_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; 
lean_dec(v___x_4164_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4167_;
}
else
{
lean_object* v_patType_x3f_4168_; lean_object* v___x_4169_; 
v_patType_x3f_4168_ = l_Lean_Syntax_getArg(v___x_4164_, v___x_4129_);
lean_dec(v___x_4164_);
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_patType_x3f_4168_);
v_patType_x3f_4131_ = v___x_4169_;
v___y_4132_ = v_a_4024_;
v___y_4133_ = v_a_4025_;
v___y_4134_ = v_a_4026_;
v___y_4135_ = v_a_4027_;
v___y_4136_ = v_a_4028_;
v___y_4137_ = v_a_4029_;
v___y_4138_ = v_a_4030_;
goto v___jp_4130_;
}
}
}
else
{
lean_object* v___x_4170_; 
lean_dec(v___x_4160_);
v___x_4170_ = lean_box(0);
v_patType_x3f_4131_ = v___x_4170_;
v___y_4132_ = v_a_4024_;
v___y_4133_ = v_a_4025_;
v___y_4134_ = v_a_4026_;
v___y_4135_ = v_a_4027_;
v___y_4136_ = v_a_4028_;
v___y_4137_ = v_a_4029_;
v___y_4138_ = v_a_4030_;
goto v___jp_4130_;
}
v___jp_4130_:
{
lean_object* v___x_4139_; lean_object* v_rhs_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4139_ = lean_unsigned_to_nat(3u);
v_rhs_4140_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4139_);
v___x_4141_ = lean_unsigned_to_nat(4u);
v___x_4142_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4141_);
lean_dec(v_stx_4022_);
v___x_4143_ = l_Lean_Syntax_isNone(v___x_4142_);
if (v___x_4143_ == 0)
{
uint8_t v___x_4144_; 
lean_inc(v___x_4142_);
v___x_4144_ = l_Lean_Syntax_matchesNull(v___x_4142_, v___x_4139_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; 
lean_dec(v___x_4142_);
lean_dec(v_rhs_4140_);
lean_dec(v_patType_x3f_4131_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_letOrReassign_4021_);
v___x_4145_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4145_;
}
else
{
lean_object* v___x_4146_; lean_object* v_otherwise_x3f_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4146_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4147_ = l_Lean_Syntax_getArg(v___x_4142_, v___x_4129_);
v___x_4148_ = l_Lean_Syntax_getArg(v___x_4142_, v___x_4146_);
lean_dec(v___x_4142_);
v___x_4149_ = l_Lean_Syntax_getOptional_x3f(v___x_4148_);
lean_dec(v___x_4148_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_box(0);
v___y_4074_ = v___y_4136_;
v___y_4075_ = v___y_4134_;
v___y_4076_ = v_rhs_4140_;
v___y_4077_ = v___y_4137_;
v___y_4078_ = v___y_4133_;
v___y_4079_ = v___y_4135_;
v___y_4080_ = v___y_4138_;
v___y_4081_ = v_otherwise_x3f_4147_;
v___y_4082_ = v___y_4132_;
v___y_4083_ = v_patType_x3f_4131_;
v___y_4084_ = v___x_4150_;
goto v___jp_4073_;
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
v_val_4151_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4149_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_val_4151_);
lean_dec(v___x_4149_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_val_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
v___y_4074_ = v___y_4136_;
v___y_4075_ = v___y_4134_;
v___y_4076_ = v_rhs_4140_;
v___y_4077_ = v___y_4137_;
v___y_4078_ = v___y_4133_;
v___y_4079_ = v___y_4135_;
v___y_4080_ = v___y_4138_;
v___y_4081_ = v_otherwise_x3f_4147_;
v___y_4082_ = v___y_4132_;
v___y_4083_ = v_patType_x3f_4131_;
v___y_4084_ = v___x_4156_;
goto v___jp_4073_;
}
}
}
}
}
else
{
lean_object* v___x_4159_; 
lean_dec(v___x_4142_);
v___x_4159_ = lean_box(0);
v___y_4045_ = v___y_4133_;
v___y_4046_ = v___y_4132_;
v___y_4047_ = v_rhs_4140_;
v___y_4048_ = v___y_4138_;
v___y_4049_ = v___y_4135_;
v___y_4050_ = v___x_4159_;
v___y_4051_ = v___y_4134_;
v___y_4052_ = v___y_4137_;
v___y_4053_ = v___y_4136_;
v___y_4054_ = v_patType_x3f_4131_;
v___y_4055_ = v___x_4159_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v_pattern_4171_; lean_object* v___x_4172_; lean_object* v_patType_x3f_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v_pattern_4171_ = l_Lean_Syntax_getArg(v___x_4041_, v___x_4040_);
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4219_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4172_);
v___x_4220_ = l_Lean_Syntax_isNone(v___x_4219_);
if (v___x_4220_ == 0)
{
uint8_t v___x_4221_; 
lean_inc(v___x_4219_);
v___x_4221_ = l_Lean_Syntax_matchesNull(v___x_4219_, v___x_4172_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; 
lean_dec(v___x_4219_);
lean_dec(v_pattern_4171_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4223_ = l_Lean_Syntax_getArg(v___x_4219_, v___x_4040_);
lean_dec(v___x_4219_);
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4223_);
v___x_4225_ = l_Lean_Syntax_isOfKind(v___x_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; 
lean_dec(v___x_4223_);
lean_dec(v_pattern_4171_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4226_;
}
else
{
lean_object* v_patType_x3f_4227_; lean_object* v___x_4228_; 
v_patType_x3f_4227_ = l_Lean_Syntax_getArg(v___x_4223_, v___x_4172_);
lean_dec(v___x_4223_);
v___x_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_patType_x3f_4227_);
v_patType_x3f_4174_ = v___x_4228_;
v___y_4175_ = v_a_4024_;
v___y_4176_ = v_a_4025_;
v___y_4177_ = v_a_4026_;
v___y_4178_ = v_a_4027_;
v___y_4179_ = v_a_4028_;
v___y_4180_ = v_a_4029_;
v___y_4181_ = v_a_4030_;
goto v___jp_4173_;
}
}
}
else
{
lean_object* v___x_4229_; 
lean_dec(v___x_4219_);
v___x_4229_ = lean_box(0);
v_patType_x3f_4174_ = v___x_4229_;
v___y_4175_ = v_a_4024_;
v___y_4176_ = v_a_4025_;
v___y_4177_ = v_a_4026_;
v___y_4178_ = v_a_4027_;
v___y_4179_ = v_a_4028_;
v___y_4180_ = v_a_4029_;
v___y_4181_ = v_a_4030_;
goto v___jp_4173_;
}
v___jp_4173_:
{
lean_object* v___x_4182_; lean_object* v_rhs_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4182_ = lean_unsigned_to_nat(3u);
v_rhs_4183_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4182_);
v___x_4184_ = lean_unsigned_to_nat(4u);
v___x_4185_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4184_);
lean_dec(v_stx_4022_);
lean_inc(v___x_4185_);
v___x_4186_ = l_Lean_Syntax_matchesNull(v___x_4185_, v___x_4040_);
if (v___x_4186_ == 0)
{
uint8_t v___x_4187_; 
lean_dec(v_pattern_4171_);
v___x_4187_ = l_Lean_Syntax_isNone(v___x_4185_);
if (v___x_4187_ == 0)
{
uint8_t v___x_4188_; 
lean_inc(v___x_4185_);
v___x_4188_ = l_Lean_Syntax_matchesNull(v___x_4185_, v___x_4182_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; 
lean_dec(v___x_4185_);
lean_dec(v_rhs_4183_);
lean_dec(v_patType_x3f_4174_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_letOrReassign_4021_);
v___x_4189_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4189_;
}
else
{
lean_object* v___x_4190_; lean_object* v_otherwise_x3f_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4190_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4191_ = l_Lean_Syntax_getArg(v___x_4185_, v___x_4172_);
v___x_4192_ = l_Lean_Syntax_getArg(v___x_4185_, v___x_4190_);
lean_dec(v___x_4185_);
v___x_4193_ = l_Lean_Syntax_getOptional_x3f(v___x_4192_);
lean_dec(v___x_4192_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_box(0);
v___y_4117_ = v_patType_x3f_4174_;
v___y_4118_ = v___y_4179_;
v___y_4119_ = v___y_4178_;
v___y_4120_ = v___y_4177_;
v___y_4121_ = v_otherwise_x3f_4191_;
v___y_4122_ = v___y_4176_;
v___y_4123_ = v_rhs_4183_;
v___y_4124_ = v___y_4175_;
v___y_4125_ = v___y_4181_;
v___y_4126_ = v___y_4180_;
v___y_4127_ = v___x_4194_;
goto v___jp_4116_;
}
else
{
lean_object* v_val_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
v_val_4195_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4193_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_val_4195_);
lean_dec(v___x_4193_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
v___y_4117_ = v_patType_x3f_4174_;
v___y_4118_ = v___y_4179_;
v___y_4119_ = v___y_4178_;
v___y_4120_ = v___y_4177_;
v___y_4121_ = v_otherwise_x3f_4191_;
v___y_4122_ = v___y_4176_;
v___y_4123_ = v_rhs_4183_;
v___y_4124_ = v___y_4175_;
v___y_4125_ = v___y_4181_;
v___y_4126_ = v___y_4180_;
v___y_4127_ = v___x_4200_;
goto v___jp_4116_;
}
}
}
}
}
else
{
lean_object* v___x_4203_; 
lean_dec(v___x_4185_);
v___x_4203_ = lean_box(0);
v___y_4087_ = v___y_4180_;
v___y_4088_ = v___x_4203_;
v___y_4089_ = v___y_4175_;
v___y_4090_ = v___y_4179_;
v___y_4091_ = v___y_4178_;
v___y_4092_ = v_patType_x3f_4174_;
v___y_4093_ = v___y_4181_;
v___y_4094_ = v___y_4176_;
v___y_4095_ = v___y_4177_;
v___y_4096_ = v_rhs_4183_;
v___y_4097_ = v___x_4203_;
goto v___jp_4086_;
}
}
else
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v___x_4185_);
lean_dec(v___x_4041_);
lean_dec(v_letOrReassign_4021_);
v___x_4204_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4205_ = l_Lean_Core_mkFreshUserName(v___x_4204_, v___y_4180_, v___y_4181_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; uint8_t v_kind_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v_kind_4207_ = lean_ctor_get_uint8(v_dec_4023_, sizeof(void*)*3);
v___x_4208_ = l_Lean_mkIdentFrom(v_pattern_4171_, v_a_4206_, v___x_4036_);
lean_dec(v_pattern_4171_);
v___x_4209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4209_, 0, v_dec_4023_);
v___x_4210_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4208_, v_patType_x3f_4174_, v_rhs_4183_, v___x_4209_, v_kind_4207_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
return v___x_4210_;
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec(v_rhs_4183_);
lean_dec(v_patType_x3f_4174_);
lean_dec(v_pattern_4171_);
lean_dec_ref(v_dec_4023_);
v_a_4211_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4205_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4205_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
}
v___jp_4044_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4057_ = l_Lean_Core_mkFreshUserName(v___x_4056_, v___y_4052_, v___y_4048_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___y_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref(v___x_4057_);
v___x_4059_ = l_Lean_mkIdentFrom(v___x_4041_, v_a_4058_, v___x_4043_);
v___x_4060_ = lean_box(v___x_4043_);
v___x_4061_ = lean_box(v___x_4038_);
lean_inc(v___x_4059_);
v___y_4062_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4062_, 0, v_letOrReassign_4021_);
lean_closure_set(v___y_4062_, 1, v___y_4050_);
lean_closure_set(v___y_4062_, 2, v___x_4060_);
lean_closure_set(v___y_4062_, 3, v___x_4032_);
lean_closure_set(v___y_4062_, 4, v___x_4033_);
lean_closure_set(v___y_4062_, 5, v___x_4034_);
lean_closure_set(v___y_4062_, 6, v___x_4041_);
lean_closure_set(v___y_4062_, 7, v___x_4059_);
lean_closure_set(v___y_4062_, 8, v_dec_4023_);
lean_closure_set(v___y_4062_, 9, v___x_4061_);
lean_closure_set(v___y_4062_, 10, v___y_4055_);
lean_closure_set(v___y_4062_, 11, v___x_4040_);
v___x_4063_ = 0;
v___x_4064_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4059_, v___y_4054_, v___y_4047_, v___y_4062_, v___x_4063_, v___y_4046_, v___y_4045_, v___y_4051_, v___y_4049_, v___y_4053_, v___y_4052_, v___y_4048_);
return v___x_4064_;
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec(v___y_4050_);
lean_dec(v___y_4047_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_letOrReassign_4021_);
v_a_4065_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4057_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4057_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
v___jp_4073_:
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___y_4081_);
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4082_;
v___y_4047_ = v___y_4076_;
v___y_4048_ = v___y_4080_;
v___y_4049_ = v___y_4079_;
v___y_4050_ = v___x_4085_;
v___y_4051_ = v___y_4075_;
v___y_4052_ = v___y_4077_;
v___y_4053_ = v___y_4074_;
v___y_4054_ = v___y_4083_;
v___y_4055_ = v___y_4084_;
goto v___jp_4044_;
}
v___jp_4086_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4099_ = l_Lean_Core_mkFreshUserName(v___x_4098_, v___y_4087_, v___y_4093_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___y_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = l_Lean_mkIdentFrom(v___x_4041_, v_a_4100_, v___x_4036_);
v___x_4102_ = lean_box(v___x_4036_);
v___x_4103_ = lean_box(v___x_4038_);
v___x_4104_ = lean_box(v___x_4043_);
lean_inc(v___x_4101_);
v___y_4105_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4105_, 0, v_letOrReassign_4021_);
lean_closure_set(v___y_4105_, 1, v___y_4088_);
lean_closure_set(v___y_4105_, 2, v___x_4102_);
lean_closure_set(v___y_4105_, 3, v___x_4032_);
lean_closure_set(v___y_4105_, 4, v___x_4033_);
lean_closure_set(v___y_4105_, 5, v___x_4034_);
lean_closure_set(v___y_4105_, 6, v___x_4041_);
lean_closure_set(v___y_4105_, 7, v___x_4101_);
lean_closure_set(v___y_4105_, 8, v_dec_4023_);
lean_closure_set(v___y_4105_, 9, v___x_4103_);
lean_closure_set(v___y_4105_, 10, v___y_4097_);
lean_closure_set(v___y_4105_, 11, v___x_4040_);
lean_closure_set(v___y_4105_, 12, v___x_4104_);
v___x_4106_ = 0;
v___x_4107_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4101_, v___y_4092_, v___y_4096_, v___y_4105_, v___x_4106_, v___y_4089_, v___y_4094_, v___y_4095_, v___y_4091_, v___y_4090_, v___y_4087_, v___y_4093_);
return v___x_4107_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec(v___y_4092_);
lean_dec(v___y_4088_);
lean_dec(v___x_4041_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_letOrReassign_4021_);
v_a_4108_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4099_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4099_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
v___jp_4116_:
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___y_4121_);
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___x_4128_;
v___y_4089_ = v___y_4124_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4117_;
v___y_4093_ = v___y_4125_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___y_4120_;
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4127_;
goto v___jp_4086_;
}
}
}
else
{
lean_object* v___x_4230_; lean_object* v_x_4231_; lean_object* v___y_4233_; lean_object* v_xType_x3f_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v_xType_x3f_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4230_ = lean_unsigned_to_nat(0u);
v_x_4231_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4230_);
v___x_4293_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4231_);
v___x_4294_ = l_Lean_Syntax_isOfKind(v_x_4231_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; 
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4295_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4296_ = lean_unsigned_to_nat(1u);
v___x_4297_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4296_);
v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
if (v___x_4298_ == 0)
{
uint8_t v___x_4299_; 
lean_inc(v___x_4297_);
v___x_4299_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4296_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; 
lean_dec(v___x_4297_);
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4300_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; 
v___x_4301_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4230_);
lean_dec(v___x_4297_);
v___x_4302_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4301_);
v___x_4303_ = l_Lean_Syntax_isOfKind(v___x_4301_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; 
lean_dec(v___x_4301_);
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v___x_4304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4304_;
}
else
{
lean_object* v_xType_x3f_4305_; lean_object* v___x_4306_; 
v_xType_x3f_4305_ = l_Lean_Syntax_getArg(v___x_4301_, v___x_4296_);
lean_dec(v___x_4301_);
v___x_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_xType_x3f_4305_);
v_xType_x3f_4248_ = v___x_4306_;
v___y_4249_ = v_a_4024_;
v___y_4250_ = v_a_4025_;
v___y_4251_ = v_a_4026_;
v___y_4252_ = v_a_4027_;
v___y_4253_ = v_a_4028_;
v___y_4254_ = v_a_4029_;
v___y_4255_ = v_a_4030_;
goto v___jp_4247_;
}
}
}
else
{
lean_object* v___x_4307_; 
lean_dec(v___x_4297_);
v___x_4307_ = lean_box(0);
v_xType_x3f_4248_ = v___x_4307_;
v___y_4249_ = v_a_4024_;
v___y_4250_ = v_a_4025_;
v___y_4251_ = v_a_4026_;
v___y_4252_ = v_a_4027_;
v___y_4253_ = v_a_4028_;
v___y_4254_ = v_a_4029_;
v___y_4255_ = v_a_4030_;
goto v___jp_4247_;
}
}
v___jp_4232_:
{
uint8_t v_kind_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_kind_4242_ = lean_ctor_get_uint8(v_dec_4023_, sizeof(void*)*3);
v___x_4243_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4021_);
lean_dec(v_letOrReassign_4021_);
v___x_4244_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4244_, 0, v_dec_4023_);
lean_inc(v_x_4231_);
v___x_4245_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4245_, 0, lean_box(0));
lean_closure_set(v___x_4245_, 1, v___x_4243_);
lean_closure_set(v___x_4245_, 2, v_x_4231_);
lean_closure_set(v___x_4245_, 3, v___x_4244_);
v___x_4246_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4231_, v_xType_x3f_4234_, v___y_4233_, v___x_4245_, v_kind_4242_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
return v___x_4246_;
}
v___jp_4247_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4256_ = lean_unsigned_to_nat(1u);
v___x_4257_ = lean_mk_empty_array_with_capacity(v___x_4256_);
lean_inc(v_x_4231_);
v___x_4258_ = lean_array_push(v___x_4257_, v_x_4231_);
v___x_4259_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4021_, v___x_4258_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec_ref(v___x_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v___x_4260_; lean_object* v_rhs_4261_; 
lean_dec_ref(v___x_4259_);
v___x_4260_ = lean_unsigned_to_nat(3u);
v_rhs_4261_ = l_Lean_Syntax_getArg(v_stx_4022_, v___x_4260_);
lean_dec(v_stx_4022_);
if (lean_obj_tag(v_letOrReassign_4021_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4248_) == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = l_Lean_TSyntax_getId(v_x_4231_);
v___x_4263_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4262_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref(v___x_4263_);
v___x_4265_ = l_Lean_LocalDecl_type(v_a_4264_);
lean_dec(v_a_4264_);
v___x_4266_ = l_Lean_Elab_Term_exprToSyntax(v___x_4265_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref(v___x_4266_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_a_4267_);
v___y_4233_ = v_rhs_4261_;
v_xType_x3f_4234_ = v___x_4268_;
v___y_4235_ = v___y_4249_;
v___y_4236_ = v___y_4250_;
v___y_4237_ = v___y_4251_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
goto v___jp_4232_;
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_rhs_4261_);
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
v_a_4269_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4266_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4266_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_rhs_4261_);
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
v_a_4277_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4263_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4263_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
else
{
v___y_4233_ = v_rhs_4261_;
v_xType_x3f_4234_ = v_xType_x3f_4248_;
v___y_4235_ = v___y_4249_;
v___y_4236_ = v___y_4250_;
v___y_4237_ = v___y_4251_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
goto v___jp_4232_;
}
}
else
{
v___y_4233_ = v_rhs_4261_;
v_xType_x3f_4234_ = v_xType_x3f_4248_;
v___y_4235_ = v___y_4249_;
v___y_4236_ = v___y_4250_;
v___y_4237_ = v___y_4251_;
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___y_4254_;
v___y_4241_ = v___y_4255_;
goto v___jp_4232_;
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v_xType_x3f_4248_);
lean_dec(v_x_4231_);
lean_dec_ref(v_dec_4023_);
lean_dec(v_stx_4022_);
lean_dec(v_letOrReassign_4021_);
v_a_4285_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4259_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4259_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4308_, lean_object* v_stx_4309_, lean_object* v_dec_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4308_, v_stx_4309_, v_dec_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec_ref(v_a_4311_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(lean_object* v_stx_4325_){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4326_ = lean_unsigned_to_nat(2u);
v___x_4327_ = l_Lean_Syntax_getArg(v_stx_4325_, v___x_4326_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0));
v___x_4329_ = l_Lean_Syntax_isOfKind(v___x_4327_, v___x_4328_);
if (v___x_4329_ == 0)
{
return v___x_4326_;
}
else
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_unsigned_to_nat(3u);
return v___x_4330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___boxed(lean_object* v_stx_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(v_stx_4331_);
lean_dec(v_stx_4331_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx(lean_object* v_stx_4333_){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4334_ = lean_unsigned_to_nat(1u);
v___x_4335_ = l_Lean_Syntax_getArg(v_stx_4333_, v___x_4334_);
v___x_4336_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0));
v___x_4337_ = l_Lean_Syntax_isOfKind(v___x_4335_, v___x_4336_);
if (v___x_4337_ == 0)
{
return v___x_4334_;
}
else
{
lean_object* v___x_4338_; 
v___x_4338_ = lean_unsigned_to_nat(2u);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx___boxed(lean_object* v_stx_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx(v_stx_4339_);
lean_dec(v_stx_4339_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4341_, lean_object* v_dec_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v_mutTk_x3f_4353_; lean_object* v___x_4354_; lean_object* v_decl_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4351_ = lean_unsigned_to_nat(1u);
v___x_4352_ = l_Lean_Syntax_getArg(v_stx_4341_, v___x_4351_);
v_mutTk_x3f_4353_ = l_Lean_Syntax_getOptional_x3f(v___x_4352_);
lean_dec(v___x_4352_);
v___x_4354_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(v_stx_4341_);
v_decl_4355_ = l_Lean_Syntax_getArg(v_stx_4341_, v___x_4354_);
lean_dec(v___x_4354_);
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v_mutTk_x3f_4353_);
v___x_4357_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4356_, v_decl_4355_, v_dec_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4358_, lean_object* v_dec_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_Elab_Do_elabDoLet(v_stx_4358_, v_dec_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_stx_4358_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4381_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4382_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0));
v___x_4383_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__2));
v___x_4384_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4385_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4381_, v___x_4382_, v___x_4383_, v___x_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4388_, lean_object* v_dec_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v_decl_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4398_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doHaveDeclIdx(v_stx_4388_);
v_decl_4399_ = l_Lean_Syntax_getArg(v_stx_4388_, v___x_4398_);
lean_dec(v___x_4398_);
v___x_4400_ = lean_box(1);
v___x_4401_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4400_, v_decl_4399_, v_dec_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4402_, lean_object* v_dec_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_Elab_Do_elabDoHave(v_stx_4402_, v_dec_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_stx_4402_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4425_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4426_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0));
v___x_4427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__2));
v___x_4428_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4429_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4425_, v___x_4426_, v___x_4427_, v___x_4428_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4434_, lean_object* v___x_4435_, lean_object* v___x_4436_, lean_object* v___x_4437_, lean_object* v_decls_4438_, lean_object* v_a_4439_, uint8_t v___x_4440_, lean_object* v_body_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_ref_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_ref_4450_ = lean_ctor_get(v___y_4447_, 5);
v___x_4451_ = 0;
v___x_4452_ = l_Lean_SourceInfo_fromRef(v_ref_4450_, v___x_4451_);
v___x_4453_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4454_ = l_Lean_Name_mkStr4(v___x_4434_, v___x_4435_, v___x_4436_, v___x_4453_);
v___x_4455_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4452_, 4);
v___x_4456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4452_);
lean_ctor_set(v___x_4456_, 1, v___x_4455_);
v___x_4457_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4452_);
lean_ctor_set(v___x_4458_, 1, v___x_4457_);
v___x_4459_ = l_Lean_Syntax_node2(v___x_4452_, v___x_4437_, v___x_4456_, v___x_4458_);
v___x_4460_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
v___x_4461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4452_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = l_Lean_Syntax_node4(v___x_4452_, v___x_4454_, v___x_4459_, v_decls_4438_, v___x_4461_, v_body_4441_);
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_a_4439_);
v___x_4464_ = l_Lean_Elab_Term_elabTerm(v___x_4462_, v___x_4463_, v___x_4440_, v___x_4440_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4465_, lean_object* v___x_4466_, lean_object* v___x_4467_, lean_object* v___x_4468_, lean_object* v_decls_4469_, lean_object* v_a_4470_, lean_object* v___x_4471_, lean_object* v_body_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
uint8_t v___x_4790__boxed_4481_; lean_object* v_res_4482_; 
v___x_4790__boxed_4481_ = lean_unbox(v___x_4471_);
v_res_4482_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4465_, v___x_4466_, v___x_4467_, v___x_4468_, v_decls_4469_, v_a_4470_, v___x_4790__boxed_4481_, v_body_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
if (lean_obj_tag(v_a_4483_) == 0)
{
lean_object* v___x_4485_; 
v___x_4485_ = l_List_reverse___redArg(v_a_4484_);
return v___x_4485_;
}
else
{
lean_object* v_head_4486_; lean_object* v_tail_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4496_; 
v_head_4486_ = lean_ctor_get(v_a_4483_, 0);
v_tail_4487_ = lean_ctor_get(v_a_4483_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_a_4483_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4489_ = v_a_4483_;
v_isShared_4490_ = v_isSharedCheck_4496_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_tail_4487_);
lean_inc(v_head_4486_);
lean_dec(v_a_4483_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4496_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l_Lean_MessageData_ofSyntax(v_head_4486_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 1, v_a_4484_);
lean_ctor_set(v___x_4489_, 0, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_a_4484_);
v___x_4493_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
v_a_4483_ = v_tail_4487_;
v_a_4484_ = v___x_4493_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4514_ = l_Lean_stringToMessageData(v___x_4513_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4515_, lean_object* v_dec_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4525_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4526_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4515_);
v___x_4529_ = l_Lean_Syntax_isOfKind(v_stx_4515_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; 
lean_dec_ref(v_dec_4516_);
lean_dec(v_stx_4515_);
v___x_4530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4530_;
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = l_Lean_Syntax_getArg(v_stx_4515_, v___x_4531_);
v___x_4533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
v___x_4534_ = l_Lean_Syntax_isOfKind(v___x_4532_, v___x_4533_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; 
lean_dec_ref(v_dec_4516_);
lean_dec(v_stx_4515_);
v___x_4535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; lean_object* v_decls_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4536_ = lean_unsigned_to_nat(1u);
v_decls_4537_ = l_Lean_Syntax_getArg(v_stx_4515_, v___x_4536_);
lean_dec(v_stx_4515_);
v___x_4538_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4537_);
v___x_4539_ = l_Lean_Syntax_isOfKind(v_decls_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
lean_dec(v_decls_4537_);
lean_dec_ref(v_dec_4516_);
v___x_4540_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; 
lean_inc(v_decls_4537_);
v___x_4541_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4537_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v_doBlockResultType_4543_; lean_object* v___x_4544_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref(v___x_4541_);
v_doBlockResultType_4543_ = lean_ctor_get(v_a_4517_, 3);
lean_inc_ref(v_doBlockResultType_4543_);
v___x_4544_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_4543_, v_a_4517_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4546_; lean_object* v___f_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref(v___x_4544_);
v___x_4546_ = lean_box(v___x_4539_);
v___f_4547_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4547_, 0, v___x_4525_);
lean_closure_set(v___f_4547_, 1, v___x_4526_);
lean_closure_set(v___f_4547_, 2, v___x_4527_);
lean_closure_set(v___f_4547_, 3, v___x_4533_);
lean_closure_set(v___f_4547_, 4, v_decls_4537_);
lean_closure_set(v___f_4547_, 5, v_a_4545_);
lean_closure_set(v___f_4547_, 6, v___x_4546_);
v___x_4548_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4549_ = lean_array_to_list(v_a_4542_);
v___x_4550_ = lean_box(0);
v___x_4551_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4549_, v___x_4550_);
v___x_4552_ = l_Lean_MessageData_ofList(v___x_4551_);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4548_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4554_, 0, v_dec_4516_);
v___x_4555_ = lean_box(0);
v___x_4556_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4553_, v___x_4554_, v___f_4547_, v___x_4555_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
return v___x_4556_;
}
else
{
lean_dec(v_a_4542_);
lean_dec(v_decls_4537_);
lean_dec_ref(v_dec_4516_);
return v___x_4544_;
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec(v_decls_4537_);
lean_dec_ref(v_dec_4516_);
v_a_4557_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4541_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4541_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4565_, lean_object* v_dec_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4565_, v_dec_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec_ref(v_a_4567_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4583_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4584_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4585_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4586_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4587_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4583_, v___x_4584_, v___x_4585_, v___x_4586_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4603_, lean_object* v_dec_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___x_4642_; uint8_t v___x_4643_; 
v___x_4642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4603_);
v___x_4643_ = l_Lean_Syntax_isOfKind(v_stx_4603_, v___x_4642_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
lean_dec_ref(v_dec_4604_);
lean_dec(v_stx_4603_);
v___x_4644_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4644_;
}
else
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4645_ = lean_unsigned_to_nat(0u);
v___x_4646_ = l_Lean_Syntax_getArg(v_stx_4603_, v___x_4645_);
lean_dec(v_stx_4603_);
v___x_4647_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_4646_);
v___x_4648_ = l_Lean_Syntax_isOfKind(v___x_4646_, v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4649_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_4646_);
v___x_4650_ = l_Lean_Syntax_isOfKind(v___x_4646_, v___x_4649_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; 
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4651_;
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v_decl_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4653_ = lean_unsigned_to_nat(1u);
v___x_4654_ = lean_mk_empty_array_with_capacity(v___x_4653_);
v___x_4655_ = lean_array_push(v___x_4654_, v___x_4646_);
v___x_4656_ = lean_box(2);
v_decl_4657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_4657_, 0, v___x_4656_);
lean_ctor_set(v_decl_4657_, 1, v___x_4652_);
lean_ctor_set(v_decl_4657_, 2, v___x_4655_);
v___x_4658_ = lean_box(2);
v___x_4659_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4658_, v_decl_4657_, v_dec_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
return v___x_4659_;
}
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v___x_4660_ = l_Lean_Syntax_getArg(v___x_4646_, v___x_4645_);
v___x_4661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4660_);
v___x_4662_ = l_Lean_Syntax_isOfKind(v___x_4660_, v___x_4661_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; 
lean_dec(v___x_4660_);
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4663_;
}
else
{
lean_object* v___x_4664_; lean_object* v_xType_x3f_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4664_ = l_Lean_Syntax_getArg(v___x_4660_, v___x_4645_);
lean_dec(v___x_4660_);
v___x_4691_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4664_);
v___x_4692_ = l_Lean_Syntax_isOfKind(v___x_4664_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
lean_dec(v___x_4664_);
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4693_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4693_;
}
else
{
lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4694_ = lean_unsigned_to_nat(1u);
v___x_4695_ = l_Lean_Syntax_getArg(v___x_4646_, v___x_4694_);
v___x_4696_ = l_Lean_Syntax_matchesNull(v___x_4695_, v___x_4645_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; 
lean_dec(v___x_4664_);
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4697_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4697_;
}
else
{
lean_object* v___x_4698_; lean_object* v___x_4699_; uint8_t v___x_4700_; 
v___x_4698_ = lean_unsigned_to_nat(2u);
v___x_4699_ = l_Lean_Syntax_getArg(v___x_4646_, v___x_4698_);
v___x_4700_ = l_Lean_Syntax_isNone(v___x_4699_);
if (v___x_4700_ == 0)
{
uint8_t v___x_4701_; 
lean_inc(v___x_4699_);
v___x_4701_ = l_Lean_Syntax_matchesNull(v___x_4699_, v___x_4694_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; 
lean_dec(v___x_4699_);
lean_dec(v___x_4664_);
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4702_;
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; 
v___x_4703_ = l_Lean_Syntax_getArg(v___x_4699_, v___x_4645_);
lean_dec(v___x_4699_);
v___x_4704_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4703_);
v___x_4705_ = l_Lean_Syntax_isOfKind(v___x_4703_, v___x_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; 
lean_dec(v___x_4703_);
lean_dec(v___x_4664_);
lean_dec(v___x_4646_);
lean_dec_ref(v_dec_4604_);
v___x_4706_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4706_;
}
else
{
lean_object* v_xType_x3f_4707_; lean_object* v___x_4708_; 
v_xType_x3f_4707_ = l_Lean_Syntax_getArg(v___x_4703_, v___x_4694_);
lean_dec(v___x_4703_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v_xType_x3f_4707_);
v_xType_x3f_4666_ = v___x_4708_;
v___y_4667_ = v_a_4605_;
v___y_4668_ = v_a_4606_;
v___y_4669_ = v_a_4607_;
v___y_4670_ = v_a_4608_;
v___y_4671_ = v_a_4609_;
v___y_4672_ = v_a_4610_;
v___y_4673_ = v_a_4611_;
goto v___jp_4665_;
}
}
}
else
{
lean_object* v___x_4709_; 
lean_dec(v___x_4699_);
v___x_4709_ = lean_box(0);
v_xType_x3f_4666_ = v___x_4709_;
v___y_4667_ = v_a_4605_;
v___y_4668_ = v_a_4606_;
v___y_4669_ = v_a_4607_;
v___y_4670_ = v_a_4608_;
v___y_4671_ = v_a_4609_;
v___y_4672_ = v_a_4610_;
v___y_4673_ = v_a_4611_;
goto v___jp_4665_;
}
}
}
v___jp_4665_:
{
lean_object* v_ref_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; uint8_t v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v_ref_4674_ = lean_ctor_get(v___y_4672_, 5);
v___x_4675_ = lean_unsigned_to_nat(4u);
v___x_4676_ = l_Lean_Syntax_getArg(v___x_4646_, v___x_4675_);
lean_dec(v___x_4646_);
v___x_4677_ = 0;
v___x_4678_ = l_Lean_SourceInfo_fromRef(v_ref_4674_, v___x_4677_);
v___x_4679_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_4678_, 2);
v___x_4680_ = l_Lean_Syntax_node1(v___x_4678_, v___x_4661_, v___x_4664_);
v___x_4681_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4682_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4678_);
lean_ctor_set(v___x_4683_, 1, v___x_4681_);
lean_ctor_set(v___x_4683_, 2, v___x_4682_);
if (lean_obj_tag(v_xType_x3f_4666_) == 1)
{
lean_object* v_val_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v_val_4684_ = lean_ctor_get(v_xType_x3f_4666_, 0);
lean_inc(v_val_4684_);
lean_dec_ref(v_xType_x3f_4666_);
v___x_4685_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4686_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4678_, 2);
v___x_4687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4678_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_Syntax_node2(v___x_4678_, v___x_4685_, v___x_4687_, v_val_4684_);
v___x_4689_ = l_Array_mkArray1___redArg(v___x_4688_);
v___y_4614_ = v___x_4678_;
v___y_4615_ = v___y_4669_;
v___y_4616_ = v___y_4673_;
v___y_4617_ = v___x_4682_;
v___y_4618_ = v___x_4681_;
v___y_4619_ = v___x_4680_;
v___y_4620_ = v___y_4667_;
v___y_4621_ = v___y_4668_;
v___y_4622_ = v___x_4683_;
v___y_4623_ = v___x_4679_;
v___y_4624_ = v___x_4676_;
v___y_4625_ = v___y_4672_;
v___y_4626_ = v___y_4671_;
v___y_4627_ = v___y_4670_;
v___y_4628_ = v___x_4689_;
goto v___jp_4613_;
}
else
{
lean_object* v___x_4690_; 
lean_dec(v_xType_x3f_4666_);
v___x_4690_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4614_ = v___x_4678_;
v___y_4615_ = v___y_4669_;
v___y_4616_ = v___y_4673_;
v___y_4617_ = v___x_4682_;
v___y_4618_ = v___x_4681_;
v___y_4619_ = v___x_4680_;
v___y_4620_ = v___y_4667_;
v___y_4621_ = v___y_4668_;
v___y_4622_ = v___x_4683_;
v___y_4623_ = v___x_4679_;
v___y_4624_ = v___x_4676_;
v___y_4625_ = v___y_4672_;
v___y_4626_ = v___y_4671_;
v___y_4627_ = v___y_4670_;
v___y_4628_ = v___x_4690_;
goto v___jp_4613_;
}
}
}
}
}
v___jp_4613_:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
lean_inc_ref(v___y_4617_);
v___x_4629_ = l_Array_append___redArg(v___y_4617_, v___y_4628_);
lean_dec_ref(v___y_4628_);
lean_inc(v___y_4618_);
lean_inc_n(v___y_4614_, 2);
v___x_4630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___y_4614_);
lean_ctor_set(v___x_4630_, 1, v___y_4618_);
lean_ctor_set(v___x_4630_, 2, v___x_4629_);
v___x_4631_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___y_4614_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
lean_inc(v___y_4623_);
v___x_4633_ = l_Lean_Syntax_node5(v___y_4614_, v___y_4623_, v___y_4619_, v___y_4622_, v___x_4630_, v___x_4632_, v___y_4624_);
v___x_4634_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4635_ = lean_unsigned_to_nat(1u);
v___x_4636_ = lean_mk_empty_array_with_capacity(v___x_4635_);
v___x_4637_ = lean_array_push(v___x_4636_, v___x_4633_);
v___x_4638_ = lean_box(2);
v___x_4639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v___x_4634_);
lean_ctor_set(v___x_4639_, 2, v___x_4637_);
v___x_4640_ = lean_box(2);
v___x_4641_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4640_, v___x_4639_, v_dec_4604_, v___y_4620_, v___y_4621_, v___y_4615_, v___y_4627_, v___y_4626_, v___y_4625_, v___y_4616_);
return v___x_4641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_4710_, lean_object* v_dec_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Lean_Elab_Do_elabDoReassign(v_stx_4710_, v_dec_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4728_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4729_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_4730_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_4731_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_4732_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4728_, v___x_4729_, v___x_4730_, v___x_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_4754_, size_t v_sz_4755_, size_t v_i_4756_, lean_object* v_b_4757_, lean_object* v___y_4758_){
_start:
{
uint8_t v___x_4760_; 
v___x_4760_ = lean_usize_dec_lt(v_i_4756_, v_sz_4755_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v_b_4757_);
return v___x_4761_;
}
else
{
lean_object* v_ref_4762_; lean_object* v___x_4763_; lean_object* v_a_4764_; uint8_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; size_t v___x_4799_; size_t v___x_4800_; 
v_ref_4762_ = lean_ctor_get(v___y_4758_, 5);
v___x_4763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4764_ = lean_array_uget_borrowed(v_as_4754_, v_i_4756_);
v___x_4765_ = 0;
v___x_4766_ = l_Lean_SourceInfo_fromRef(v_ref_4762_, v___x_4765_);
v___x_4767_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4769_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0));
v___x_4770_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4766_, 17);
v___x_4771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4766_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4766_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4767_, v___x_4773_);
v___x_4775_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0));
v___x_4776_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4766_);
lean_ctor_set(v___x_4777_, 1, v___x_4767_);
lean_ctor_set(v___x_4777_, 2, v___x_4776_);
lean_inc_ref_n(v___x_4777_, 3);
v___x_4778_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4775_, v___x_4777_);
v___x_4779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4780_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_4764_, 2);
v___x_4782_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4781_, v_a_4764_);
v___x_4783_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4766_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = l_Lean_Syntax_node5(v___x_4766_, v___x_4780_, v___x_4782_, v___x_4777_, v___x_4777_, v___x_4784_, v_a_4764_);
v___x_4786_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4779_, v___x_4785_);
v___x_4787_ = l_Lean_Syntax_node4(v___x_4766_, v___x_4769_, v___x_4771_, v___x_4774_, v___x_4778_, v___x_4786_);
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
v___x_4789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4766_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4767_, v___x_4789_);
v___x_4791_ = l_Lean_Syntax_node2(v___x_4766_, v___x_4768_, v___x_4787_, v___x_4790_);
v___x_4792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_4794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4766_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l_Lean_Syntax_node2(v___x_4766_, v___x_4792_, v___x_4794_, v_b_4757_);
v___x_4796_ = l_Lean_Syntax_node2(v___x_4766_, v___x_4768_, v___x_4795_, v___x_4777_);
v___x_4797_ = l_Lean_Syntax_node2(v___x_4766_, v___x_4767_, v___x_4791_, v___x_4796_);
v___x_4798_ = l_Lean_Syntax_node1(v___x_4766_, v___x_4763_, v___x_4797_);
v___x_4799_ = ((size_t)1ULL);
v___x_4800_ = lean_usize_add(v_i_4756_, v___x_4799_);
v_i_4756_ = v___x_4800_;
v_b_4757_ = v___x_4798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_4802_, lean_object* v_sz_4803_, lean_object* v_i_4804_, lean_object* v_b_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
size_t v_sz_boxed_4808_; size_t v_i_boxed_4809_; lean_object* v_res_4810_; 
v_sz_boxed_4808_ = lean_unbox_usize(v_sz_4803_);
lean_dec(v_sz_4803_);
v_i_boxed_4809_ = lean_unbox_usize(v_i_4804_);
lean_dec(v_i_4804_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4802_, v_sz_boxed_4808_, v_i_boxed_4809_, v_b_4805_, v___y_4806_);
lean_dec_ref(v___y_4806_);
lean_dec_ref(v_as_4802_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_4811_, size_t v_sz_4812_, size_t v_i_4813_, lean_object* v_b_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
uint8_t v___x_4823_; 
v___x_4823_ = lean_usize_dec_lt(v_i_4813_, v_sz_4812_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; 
v___x_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4824_, 0, v_b_4814_);
return v___x_4824_;
}
else
{
lean_object* v_ref_4825_; lean_object* v___x_4826_; lean_object* v_a_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; size_t v___x_4862_; size_t v___x_4863_; lean_object* v___x_4864_; 
v_ref_4825_ = lean_ctor_get(v___y_4820_, 5);
v___x_4826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_4827_ = lean_array_uget_borrowed(v_as_4811_, v_i_4813_);
v___x_4828_ = 0;
v___x_4829_ = l_Lean_SourceInfo_fromRef(v_ref_4825_, v___x_4828_);
v___x_4830_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_4832_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0));
v___x_4833_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4829_, 17);
v___x_4834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4829_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4829_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
v___x_4837_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4830_, v___x_4836_);
v___x_4838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx___closed__0));
v___x_4839_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4829_);
lean_ctor_set(v___x_4840_, 1, v___x_4830_);
lean_ctor_set(v___x_4840_, 2, v___x_4839_);
lean_inc_ref_n(v___x_4840_, 3);
v___x_4841_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4838_, v___x_4840_);
v___x_4842_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_4844_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_4827_, 2);
v___x_4845_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4844_, v_a_4827_);
v___x_4846_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4829_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
v___x_4848_ = l_Lean_Syntax_node5(v___x_4829_, v___x_4843_, v___x_4845_, v___x_4840_, v___x_4840_, v___x_4847_, v_a_4827_);
v___x_4849_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4842_, v___x_4848_);
v___x_4850_ = l_Lean_Syntax_node4(v___x_4829_, v___x_4832_, v___x_4834_, v___x_4837_, v___x_4841_, v___x_4849_);
v___x_4851_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__7));
v___x_4852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4829_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
v___x_4853_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4830_, v___x_4852_);
v___x_4854_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4831_, v___x_4850_, v___x_4853_);
v___x_4855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_4856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_4857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4829_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4855_, v___x_4857_, v_b_4814_);
v___x_4859_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4831_, v___x_4858_, v___x_4840_);
v___x_4860_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4830_, v___x_4854_, v___x_4859_);
v___x_4861_ = l_Lean_Syntax_node1(v___x_4829_, v___x_4826_, v___x_4860_);
v___x_4862_ = ((size_t)1ULL);
v___x_4863_ = lean_usize_add(v_i_4813_, v___x_4862_);
v___x_4864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_4811_, v_sz_4812_, v___x_4863_, v___x_4861_, v___y_4820_);
return v___x_4864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_4865_, lean_object* v_sz_4866_, lean_object* v_i_4867_, lean_object* v_b_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
size_t v_sz_boxed_4877_; size_t v_i_boxed_4878_; lean_object* v_res_4879_; 
v_sz_boxed_4877_ = lean_unbox_usize(v_sz_4866_);
lean_dec(v_sz_4866_);
v_i_boxed_4878_ = lean_unbox_usize(v_i_4867_);
lean_dec(v_i_4867_);
v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_4865_, v_sz_boxed_4877_, v_i_boxed_4878_, v_b_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_as_4865_);
return v_res_4879_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__10(void){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_4915_ = l_String_toRawSubstring_x27(v___x_4914_);
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__17(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_4930_ = l_String_toRawSubstring_x27(v___x_4929_);
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_4947_, lean_object* v_dec_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v_mutTk_x3f_4959_; lean_object* v_offset_4960_; lean_object* v_pattern_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v_body_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_5014_; lean_object* v_a_5015_; lean_object* v___y_5029_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_4957_ = lean_unsigned_to_nat(1u);
v___x_4958_ = l_Lean_Syntax_getArg(v_stx_4947_, v___x_4957_);
v_mutTk_x3f_4959_ = l_Lean_Syntax_getOptional_x3f(v___x_4958_);
lean_dec(v___x_4958_);
v_offset_4960_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(v_stx_4947_);
v_pattern_4961_ = l_Lean_Syntax_getArg(v_stx_4947_, v_offset_4960_);
v___x_4962_ = lean_unsigned_to_nat(2u);
v___x_4963_ = lean_nat_add(v_offset_4960_, v___x_4962_);
v___x_4964_ = l_Lean_Syntax_getArg(v_stx_4947_, v___x_4963_);
lean_dec(v___x_4963_);
v___x_4965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_4966_ = lean_unsigned_to_nat(4u);
v___x_4967_ = lean_nat_add(v_offset_4960_, v___x_4966_);
v___x_4968_ = l_Lean_Syntax_getArg(v_stx_4947_, v___x_4967_);
lean_dec(v___x_4967_);
v___x_5078_ = lean_unsigned_to_nat(5u);
v___x_5079_ = lean_nat_add(v_offset_4960_, v___x_5078_);
lean_dec(v_offset_4960_);
v___x_5080_ = l_Lean_Syntax_getArg(v_stx_4947_, v___x_5079_);
lean_dec(v___x_5079_);
v___x_5081_ = l_Lean_Syntax_getOptional_x3f(v___x_5080_);
lean_dec(v___x_5080_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_box(0);
v___y_5029_ = v___x_5082_;
goto v___jp_5028_;
}
else
{
lean_object* v_val_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
v_val_5083_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5081_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_val_5083_);
lean_dec(v___x_5081_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_val_5083_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
v___y_5029_ = v___x_5088_;
goto v___jp_5028_;
}
}
}
v___jp_4969_:
{
lean_object* v_ref_4978_; uint8_t v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; lean_object* v___x_5012_; 
v_ref_4978_ = lean_ctor_get(v___y_4976_, 5);
v___x_4979_ = 0;
v___x_4980_ = l_Lean_SourceInfo_fromRef(v_ref_4978_, v___x_4979_);
v___x_4981_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_4982_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__10));
lean_inc_n(v___x_4980_, 17);
v___x_4983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4980_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4985_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4980_);
lean_ctor_set(v___x_4986_, 1, v___x_4984_);
lean_ctor_set(v___x_4986_, 2, v___x_4985_);
v___x_4987_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
lean_inc_ref_n(v___x_4986_, 3);
v___x_4988_ = l_Lean_Syntax_node2(v___x_4980_, v___x_4987_, v___x_4986_, v___x_4964_);
v___x_4989_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4984_, v___x_4988_);
v___x_4990_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__18));
v___x_4991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4980_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_4993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_4994_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__21));
v___x_4995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4980_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4984_, v_pattern_4961_);
v___x_4997_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4984_, v___x_4996_);
v___x_4998_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__22));
v___x_4999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4980_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
lean_inc_ref(v___x_4999_);
lean_inc_ref(v___x_4995_);
v___x_5000_ = l_Lean_Syntax_node4(v___x_4980_, v___x_4993_, v___x_4995_, v___x_4997_, v___x_4999_, v_body_4970_);
v___x_5001_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5002_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___closed__15));
v___x_5003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___x_4980_);
lean_ctor_set(v___x_5003_, 1, v___x_5002_);
v___x_5004_ = l_Lean_Syntax_node1(v___x_4980_, v___x_5001_, v___x_5003_);
v___x_5005_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4984_, v___x_5004_);
v___x_5006_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4984_, v___x_5005_);
v___x_5007_ = l_Lean_Syntax_node4(v___x_4980_, v___x_4993_, v___x_4995_, v___x_5006_, v___x_4999_, v___x_4968_);
v___x_5008_ = l_Lean_Syntax_node2(v___x_4980_, v___x_4984_, v___x_5000_, v___x_5007_);
v___x_5009_ = l_Lean_Syntax_node1(v___x_4980_, v___x_4992_, v___x_5008_);
v___x_5010_ = l_Lean_Syntax_node7(v___x_4980_, v___x_4981_, v___x_4983_, v___x_4986_, v___x_4986_, v___x_4986_, v___x_4989_, v___x_4991_, v___x_5009_);
v___x_5011_ = 1;
v___x_5012_ = l_Lean_Elab_Do_elabDoElem(v___x_5010_, v_dec_4948_, v___x_5011_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_5012_;
}
v___jp_5013_:
{
if (lean_obj_tag(v_mutTk_x3f_4959_) == 0)
{
lean_dec_ref(v___y_5014_);
v_body_4970_ = v_a_5015_;
v___y_4971_ = v_a_4949_;
v___y_4972_ = v_a_4950_;
v___y_4973_ = v_a_4951_;
v___y_4974_ = v_a_4952_;
v___y_4975_ = v_a_4953_;
v___y_4976_ = v_a_4954_;
v___y_4977_ = v_a_4955_;
goto v___jp_4969_;
}
else
{
size_t v_sz_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
lean_dec_ref(v_mutTk_x3f_4959_);
v_sz_5016_ = lean_array_size(v___y_5014_);
v___x_5017_ = ((size_t)0ULL);
v___x_5018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5014_, v_sz_5016_, v___x_5017_, v_a_5015_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
lean_dec_ref(v___y_5014_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref(v___x_5018_);
v_body_4970_ = v_a_5019_;
v___y_4971_ = v_a_4949_;
v___y_4972_ = v_a_4950_;
v___y_4973_ = v_a_4951_;
v___y_4974_ = v_a_4952_;
v___y_4975_ = v_a_4953_;
v___y_4976_ = v_a_4954_;
v___y_4977_ = v_a_4955_;
goto v___jp_4969_;
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v___x_4968_);
lean_dec(v___x_4964_);
lean_dec(v_pattern_4961_);
lean_dec_ref(v_dec_4948_);
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
v___jp_5028_:
{
lean_object* v___x_5030_; 
lean_inc(v_pattern_4961_);
v___x_5030_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_4961_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v_letOrReassign_5032_; lean_object* v___x_5033_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref(v___x_5030_);
lean_inc(v_mutTk_x3f_4959_);
v_letOrReassign_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_letOrReassign_5032_, 0, v_mutTk_x3f_4959_);
v___x_5033_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_5032_, v_a_5031_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
lean_dec_ref(v_letOrReassign_5032_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_dec_ref(v___x_5033_);
if (lean_obj_tag(v___y_5029_) == 0)
{
lean_object* v_ref_5034_; lean_object* v_quotContext_5035_; lean_object* v_currMacroScope_5036_; uint8_t v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_ref_5034_ = lean_ctor_get(v_a_4954_, 5);
v_quotContext_5035_ = lean_ctor_get(v_a_4954_, 10);
v_currMacroScope_5036_ = lean_ctor_get(v_a_4954_, 11);
v___x_5037_ = 0;
v___x_5038_ = l_Lean_SourceInfo_fromRef(v_ref_5034_, v___x_5037_);
v___x_5039_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5041_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5042_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__8));
v___x_5043_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__10, &l_Lean_Elab_Do_elabDoLetElse___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__10);
v___x_5044_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__11));
lean_inc_n(v_currMacroScope_5036_, 2);
lean_inc_n(v_quotContext_5035_, 2);
v___x_5045_ = l_Lean_addMacroScope(v_quotContext_5035_, v___x_5044_, v_currMacroScope_5036_);
v___x_5046_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__15));
lean_inc_n(v___x_5038_, 8);
v___x_5047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5038_);
lean_ctor_set(v___x_5047_, 1, v___x_5043_);
lean_ctor_set(v___x_5047_, 2, v___x_5045_);
lean_ctor_set(v___x_5047_, 3, v___x_5046_);
v___x_5048_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__17, &l_Lean_Elab_Do_elabDoLetElse___closed__17_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__17);
v___x_5049_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__20));
v___x_5050_ = l_Lean_addMacroScope(v_quotContext_5035_, v___x_5049_, v_currMacroScope_5036_);
v___x_5051_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__24));
v___x_5052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5038_);
lean_ctor_set(v___x_5052_, 1, v___x_5048_);
lean_ctor_set(v___x_5052_, 2, v___x_5050_);
lean_ctor_set(v___x_5052_, 3, v___x_5051_);
v___x_5053_ = l_Lean_Syntax_node1(v___x_5038_, v___x_5039_, v___x_5052_);
v___x_5054_ = l_Lean_Syntax_node2(v___x_5038_, v___x_5042_, v___x_5047_, v___x_5053_);
v___x_5055_ = l_Lean_Syntax_node1(v___x_5038_, v___x_5041_, v___x_5054_);
v___x_5056_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5038_);
lean_ctor_set(v___x_5057_, 1, v___x_5039_);
lean_ctor_set(v___x_5057_, 2, v___x_5056_);
v___x_5058_ = l_Lean_Syntax_node2(v___x_5038_, v___x_5040_, v___x_5055_, v___x_5057_);
v___x_5059_ = l_Lean_Syntax_node1(v___x_5038_, v___x_5039_, v___x_5058_);
v___x_5060_ = l_Lean_Syntax_node1(v___x_5038_, v___x_4965_, v___x_5059_);
v___y_5014_ = v_a_5031_;
v_a_5015_ = v___x_5060_;
goto v___jp_5013_;
}
else
{
lean_object* v_val_5061_; 
v_val_5061_ = lean_ctor_get(v___y_5029_, 0);
lean_inc(v_val_5061_);
lean_dec_ref(v___y_5029_);
v___y_5014_ = v_a_5031_;
v_a_5015_ = v_val_5061_;
goto v___jp_5013_;
}
}
else
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5069_; 
lean_dec(v_a_5031_);
lean_dec(v___y_5029_);
lean_dec(v___x_4968_);
lean_dec(v___x_4964_);
lean_dec(v_pattern_4961_);
lean_dec(v_mutTk_x3f_4959_);
lean_dec_ref(v_dec_4948_);
v_a_5062_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5064_ = v___x_5033_;
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5033_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec(v___y_5029_);
lean_dec(v___x_4968_);
lean_dec(v___x_4964_);
lean_dec(v_pattern_4961_);
lean_dec(v_mutTk_x3f_4959_);
lean_dec_ref(v_dec_4948_);
v_a_5070_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5030_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5030_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5091_, lean_object* v_dec_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5091_, v_dec_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec_ref(v_a_5093_);
lean_dec(v_stx_5091_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5102_, size_t v_sz_5103_, size_t v_i_5104_, lean_object* v_b_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v___x_5114_; 
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5102_, v_sz_5103_, v_i_5104_, v_b_5105_, v___y_5111_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5115_, lean_object* v_sz_5116_, lean_object* v_i_5117_, lean_object* v_b_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
size_t v_sz_boxed_5127_; size_t v_i_boxed_5128_; lean_object* v_res_5129_; 
v_sz_boxed_5127_ = lean_unbox_usize(v_sz_5116_);
lean_dec(v_sz_5116_);
v_i_boxed_5128_ = lean_unbox_usize(v_i_5117_);
lean_dec(v_i_5117_);
v_res_5129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5115_, v_sz_boxed_5127_, v_i_boxed_5128_, v_b_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_as_5115_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5142_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0));
v___x_5144_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__2));
v___x_5145_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5146_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5142_, v___x_5143_, v___x_5144_, v___x_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l_Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5149_, lean_object* v_dec_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v_mutTk_x3f_5161_; lean_object* v___x_5162_; lean_object* v_decl_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5159_ = lean_unsigned_to_nat(1u);
v___x_5160_ = l_Lean_Syntax_getArg(v_stx_5149_, v___x_5159_);
v_mutTk_x3f_5161_ = l_Lean_Syntax_getOptional_x3f(v___x_5160_);
lean_dec(v___x_5160_);
v___x_5162_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_doLetDeclIdx(v_stx_5149_);
v_decl_5163_ = l_Lean_Syntax_getArg(v_stx_5149_, v___x_5162_);
lean_dec(v___x_5162_);
v___x_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5164_, 0, v_mutTk_x3f_5161_);
v___x_5165_ = l_Lean_Elab_Do_elabDoArrow(v___x_5164_, v_decl_5163_, v_dec_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5166_, lean_object* v_dec_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5166_, v_dec_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
lean_dec(v_a_5172_);
lean_dec_ref(v_a_5171_);
lean_dec(v_a_5170_);
lean_dec_ref(v_a_5169_);
lean_dec_ref(v_a_5168_);
lean_dec(v_stx_5166_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5190_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5191_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5192_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__3));
v___x_5193_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5194_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5190_, v___x_5191_, v___x_5192_, v___x_5193_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5203_, lean_object* v_dec_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v___x_5213_; uint8_t v___x_5214_; 
v___x_5213_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5203_);
v___x_5214_ = l_Lean_Syntax_isOfKind(v_stx_5203_, v___x_5213_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; 
lean_dec_ref(v_dec_5204_);
lean_dec(v_stx_5203_);
v___x_5215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5215_;
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; uint8_t v___x_5219_; 
v___x_5216_ = lean_unsigned_to_nat(0u);
v___x_5217_ = l_Lean_Syntax_getArg(v_stx_5203_, v___x_5216_);
lean_dec(v_stx_5203_);
v___x_5218_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5217_);
v___x_5219_ = l_Lean_Syntax_isOfKind(v___x_5217_, v___x_5218_);
if (v___x_5219_ == 0)
{
lean_object* v___x_5220_; uint8_t v___x_5221_; 
v___x_5220_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5217_);
v___x_5221_ = l_Lean_Syntax_isOfKind(v___x_5217_, v___x_5220_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; 
lean_dec(v___x_5217_);
lean_dec_ref(v_dec_5204_);
v___x_5222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5222_;
}
else
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5223_ = lean_box(2);
v___x_5224_ = l_Lean_Elab_Do_elabDoArrow(v___x_5223_, v___x_5217_, v_dec_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
return v___x_5224_;
}
}
else
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = lean_box(2);
v___x_5226_ = l_Lean_Elab_Do_elabDoArrow(v___x_5225_, v___x_5217_, v_dec_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
return v___x_5226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5227_, lean_object* v_dec_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5227_, v_dec_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
lean_dec_ref(v_a_5232_);
lean_dec(v_a_5231_);
lean_dec_ref(v_a_5230_);
lean_dec_ref(v_a_5229_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5245_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5246_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5247_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5248_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5249_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5245_, v___x_5246_, v___x_5247_, v___x_5248_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5251_;
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
