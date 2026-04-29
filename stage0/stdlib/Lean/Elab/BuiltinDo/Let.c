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
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_throwUnlessMutVarsDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandLetEqnsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "`+generalize` is not supported in `do` blocks"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`+postponeValue` is not supported in `do` blocks"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "let_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "waitIfTypeMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "wait_if_type_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object**);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoArrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__x"};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__5_value),LEAN_SCALAR_PTR_LITERAL(238, 215, 60, 46, 39, 217, 189, 106)}};
static const lean_object* l_Lean_Elab_Do_elabDoArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "configuration options are not allowed with `let mut`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoLet"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 0, 15, 120, 200, 84, 91, 220)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoHave"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 115, 123, 116, 44, 216, 133, 101)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoLetRec"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 245, 136, 148, 64, 2, 202, 185)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoReassign"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 53, 237, 208, 54, 227, 67, 171)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabDoLetElse"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 42, 180, 235, 57, 50, 131, 26)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 48, .m_data = "configuration options are not supported with `←`"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetArrow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabDoLetArrow"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 6, 18, 178, 201, 235, 246, 214)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabDoReassignArrow"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 247, 22, 101, 121, 153, 219, 18)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object*);
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
v___x_597_ = l_Lean_Elab_getBetterRef(v_ref_593_, v_macroStack_596_);
lean_inc(v_macroStack_596_);
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
v___x_885_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_874_, v_a_883_, v___x_721_, v___x_721_, v___x_884_, v___y_882_, v___y_881_, v___y_880_, v___y_877_, v___y_879_, v___y_878_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v___x_885_);
v___x_886_ = l_Lean_TSyntax_getId(v_x_874_);
v___x_887_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_886_, v___y_880_, v___y_877_, v___y_879_, v___y_878_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = l_Lean_LocalDecl_type(v_a_888_);
lean_dec(v_a_888_);
v___x_890_ = l_Lean_Elab_Term_exprToSyntax(v___x_889_, v___y_882_, v___y_881_, v___y_880_, v___y_877_, v___y_879_, v___y_878_);
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
v___y_877_ = v___y_936_;
v___y_878_ = v___y_938_;
v___y_879_ = v___y_937_;
v___y_880_ = v___y_935_;
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
v___y_877_ = v___y_936_;
v___y_878_ = v___y_938_;
v___y_879_ = v___y_937_;
v___y_880_ = v___y_935_;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_ref_1048_; lean_object* v___x_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_ref_1048_ = lean_ctor_get(v___y_1045_, 5);
v___x_1049_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_inc(v_ref_1048_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_ref_1048_);
lean_ctor_set(v___x_1054_, 1, v_a_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 1);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1065_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
uint8_t v_postponeValue_1081_; uint8_t v_generalize_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; 
v_postponeValue_1081_ = lean_ctor_get_uint8(v_config_1072_, sizeof(void*)*1 + 3);
v_generalize_1082_ = lean_ctor_get_uint8(v_config_1072_, sizeof(void*)*1 + 4);
if (v_postponeValue_1081_ == 0)
{
v___y_1084_ = v_a_1073_;
v___y_1085_ = v_a_1074_;
v___y_1086_ = v_a_1075_;
v___y_1087_ = v_a_1076_;
v___y_1088_ = v_a_1077_;
v___y_1089_ = v_a_1078_;
v___y_1090_ = v_a_1079_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_1096_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1095_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
return v___x_1096_;
}
v___jp_1083_:
{
if (v_generalize_1082_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_1094_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1093_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec_ref(v_config_1097_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_1107_, lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1108_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_1118_, v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1128_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_keyedConfig_1166_; uint8_t v_trackZetaDelta_1167_; lean_object* v_zetaDeltaSet_1168_; lean_object* v_localInstances_1169_; lean_object* v_defEqCtx_x3f_1170_; lean_object* v_synthPendingDepth_1171_; lean_object* v_canUnfold_x3f_1172_; uint8_t v_univApprox_1173_; uint8_t v_inTypeClassResolution_1174_; uint8_t v_cacheInferType_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_keyedConfig_1166_ = lean_ctor_get(v___y_1161_, 0);
v_trackZetaDelta_1167_ = lean_ctor_get_uint8(v___y_1161_, sizeof(void*)*7);
v_zetaDeltaSet_1168_ = lean_ctor_get(v___y_1161_, 1);
v_localInstances_1169_ = lean_ctor_get(v___y_1161_, 3);
v_defEqCtx_x3f_1170_ = lean_ctor_get(v___y_1161_, 4);
v_synthPendingDepth_1171_ = lean_ctor_get(v___y_1161_, 5);
v_canUnfold_x3f_1172_ = lean_ctor_get(v___y_1161_, 6);
v_univApprox_1173_ = lean_ctor_get_uint8(v___y_1161_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1174_ = lean_ctor_get_uint8(v___y_1161_, sizeof(void*)*7 + 2);
v_cacheInferType_1175_ = lean_ctor_get_uint8(v___y_1161_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1172_);
lean_inc(v_synthPendingDepth_1171_);
lean_inc(v_defEqCtx_x3f_1170_);
lean_inc_ref(v_localInstances_1169_);
lean_inc(v_zetaDeltaSet_1168_);
lean_inc_ref(v_keyedConfig_1166_);
v___x_1176_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1176_, 0, v_keyedConfig_1166_);
lean_ctor_set(v___x_1176_, 1, v_zetaDeltaSet_1168_);
lean_ctor_set(v___x_1176_, 2, v_lctx_1157_);
lean_ctor_set(v___x_1176_, 3, v_localInstances_1169_);
lean_ctor_set(v___x_1176_, 4, v_defEqCtx_x3f_1170_);
lean_ctor_set(v___x_1176_, 5, v_synthPendingDepth_1171_);
lean_ctor_set(v___x_1176_, 6, v_canUnfold_x3f_1172_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7, v_trackZetaDelta_1167_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 1, v_univApprox_1173_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1174_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*7 + 3, v_cacheInferType_1175_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
lean_inc(v___y_1162_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___x_1177_ = lean_apply_7(v_x_1158_, v___y_1159_, v___y_1160_, v___x_1176_, v___y_1162_, v___y_1163_, v___y_1164_, lean_box(0));
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1196_, lean_object* v_lctx_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1197_, v_x_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1207_, lean_object* v_lctx_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1207_, v_lctx_1208_, v_x_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___x_1228_ = lean_apply_9(v_k_1218_, v_b_1222_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, lean_box(0));
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v_b_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1240_, lean_object* v_type_1241_, lean_object* v_val_1242_, lean_object* v_k_1243_, uint8_t v_nondep_1244_, uint8_t v_kind_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___f_1254_; lean_object* v___x_1255_; 
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc_ref(v___y_1246_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1254_, 0, v_k_1243_);
lean_closure_set(v___f_1254_, 1, v___y_1246_);
lean_closure_set(v___f_1254_, 2, v___y_1247_);
lean_closure_set(v___f_1254_, 3, v___y_1248_);
v___x_1255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1240_, v_type_1241_, v_val_1242_, v___f_1254_, v_nondep_1244_, v_kind_1245_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1255_) == 0)
{
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1264_, lean_object* v_type_1265_, lean_object* v_val_1266_, lean_object* v_k_1267_, lean_object* v_nondep_1268_, lean_object* v_kind_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v_nondep_boxed_1278_; uint8_t v_kind_boxed_1279_; lean_object* v_res_1280_; 
v_nondep_boxed_1278_ = lean_unbox(v_nondep_1268_);
v_kind_boxed_1279_ = lean_unbox(v_kind_1269_);
v_res_1280_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1264_, v_type_1265_, v_val_1266_, v_k_1267_, v_nondep_boxed_1278_, v_kind_boxed_1279_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1281_, lean_object* v_name_1282_, lean_object* v_type_1283_, lean_object* v_val_1284_, lean_object* v_k_1285_, uint8_t v_nondep_1286_, uint8_t v_kind_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1282_, v_type_1283_, v_val_1284_, v_k_1285_, v_nondep_1286_, v_kind_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_name_1298_, lean_object* v_type_1299_, lean_object* v_val_1300_, lean_object* v_k_1301_, lean_object* v_nondep_1302_, lean_object* v_kind_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_nondep_boxed_1312_; uint8_t v_kind_boxed_1313_; lean_object* v_res_1314_; 
v_nondep_boxed_1312_ = lean_unbox(v_nondep_1302_);
v_kind_boxed_1313_ = lean_unbox(v_kind_1303_);
v_res_1314_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1297_, v_name_1298_, v_type_1299_, v_val_1300_, v_k_1301_, v_nondep_boxed_1312_, v_kind_boxed_1313_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1315_, lean_object* v___x_1316_, uint8_t v___x_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, uint8_t v___x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1315_, v___x_1316_, v___x_1317_, v___x_1317_, v___x_1318_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = 1;
v___x_1331_ = l_Lean_Meta_mkLambdaFVars(v___x_1319_, v_a_1329_, v___x_1320_, v___x_1320_, v___x_1320_, v___x_1317_, v___x_1330_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1331_;
}
else
{
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v___x_98626__boxed_1345_; uint8_t v___x_98629__boxed_1346_; lean_object* v_res_1347_; 
v___x_98626__boxed_1345_ = lean_unbox(v___x_1334_);
v___x_98629__boxed_1346_ = lean_unbox(v___x_1337_);
v_res_1347_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1332_, v___x_1333_, v___x_98626__boxed_1345_, v___x_1335_, v___x_1336_, v___x_98629__boxed_1346_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___x_1336_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1377_; 
v_ks_1352_ = lean_ctor_get(v_x_1348_, 0);
v_vs_1353_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1355_ = v_x_1348_;
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_vs_1353_);
lean_inc(v_ks_1352_);
lean_dec(v_x_1348_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_array_get_size(v_ks_1352_);
v___x_1358_ = lean_nat_dec_lt(v_x_1349_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_dec(v_x_1349_);
v___x_1359_ = lean_array_push(v_ks_1352_, v_x_1350_);
v___x_1360_ = lean_array_push(v_vs_1353_, v_x_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1362_ = v___x_1355_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v_k_x27_1364_; uint8_t v___x_1365_; 
v_k_x27_1364_ = lean_array_fget_borrowed(v_ks_1352_, v_x_1349_);
v___x_1365_ = l_Lean_instBEqFVarId_beq(v_x_1350_, v_k_x27_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1367_; 
if (v_isShared_1356_ == 0)
{
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_ks_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_vs_1353_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_x_1349_, v___x_1368_);
lean_dec(v_x_1349_);
v_x_1348_ = v___x_1367_;
v_x_1349_ = v___x_1369_;
goto _start;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_array_fset(v_ks_1352_, v_x_1349_, v_x_1350_);
v___x_1373_ = lean_array_fset(v_vs_1353_, v_x_1349_, v_x_1351_);
lean_dec(v_x_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1373_);
lean_ctor_set(v___x_1355_, 0, v___x_1372_);
v___x_1375_ = v___x_1355_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1378_, lean_object* v_k_1379_, lean_object* v_v_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1378_, v___x_1381_, v_k_1379_, v_v_1380_);
return v___x_1382_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; 
v___x_1383_ = ((size_t)5ULL);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_shift_left(v___x_1384_, v___x_1383_);
return v___x_1385_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; 
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1388_ = lean_usize_sub(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1390_, size_t v_x_1391_, size_t v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1390_) == 0)
{
lean_object* v_es_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; lean_object* v_j_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_es_1395_ = lean_ctor_get(v_x_1390_, 0);
v___x_1396_ = ((size_t)5ULL);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_1399_ = lean_usize_land(v_x_1391_, v___x_1398_);
v_j_1400_ = lean_usize_to_nat(v___x_1399_);
v___x_1401_ = lean_array_get_size(v_es_1395_);
v___x_1402_ = lean_nat_dec_lt(v_j_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_j_1400_);
lean_dec(v_x_1394_);
lean_dec(v_x_1393_);
return v_x_1390_;
}
else
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1439_; 
lean_inc_ref(v_es_1395_);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_x_1390_, 0);
lean_dec(v_unused_1440_);
v___x_1404_ = v_x_1390_;
v_isShared_1405_ = v_isSharedCheck_1439_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1439_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_v_1406_; lean_object* v___x_1407_; lean_object* v_xs_x27_1408_; lean_object* v___y_1410_; 
v_v_1406_ = lean_array_fget(v_es_1395_, v_j_1400_);
v___x_1407_ = lean_box(0);
v_xs_x27_1408_ = lean_array_fset(v_es_1395_, v_j_1400_, v___x_1407_);
switch(lean_obj_tag(v_v_1406_))
{
case 0:
{
lean_object* v_key_1415_; lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_key_1415_ = lean_ctor_get(v_v_1406_, 0);
v_val_1416_ = lean_ctor_get(v_v_1406_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_v_1406_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1418_ = v_v_1406_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_inc(v_key_1415_);
lean_dec(v_v_1406_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_instBEqFVarId_beq(v_x_1393_, v_key_1415_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1418_);
v___x_1421_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1415_, v_val_1416_, v_x_1393_, v_x_1394_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
v___y_1410_ = v___x_1422_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_val_1416_);
lean_dec(v_key_1415_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_x_1394_);
lean_ctor_set(v___x_1418_, 0, v_x_1393_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_x_1393_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_x_1394_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
v___y_1410_ = v___x_1424_;
goto v___jp_1409_;
}
}
}
}
case 1:
{
lean_object* v_node_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_node_1427_ = lean_ctor_get(v_v_1406_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_v_1406_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v_v_1406_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_node_1427_);
lean_dec(v_v_1406_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1431_ = lean_usize_shift_right(v_x_1391_, v___x_1396_);
v___x_1432_ = lean_usize_add(v_x_1392_, v___x_1397_);
v___x_1433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1427_, v___x_1431_, v___x_1432_, v_x_1393_, v_x_1394_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1433_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v___y_1410_ = v___x_1435_;
goto v___jp_1409_;
}
}
}
default: 
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_x_1393_);
lean_ctor_set(v___x_1438_, 1, v_x_1394_);
v___y_1410_ = v___x_1438_;
goto v___jp_1409_;
}
}
v___jp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_array_fset(v_xs_x27_1408_, v_j_1400_, v___y_1410_);
lean_dec(v_j_1400_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1411_);
v___x_1413_ = v___x_1404_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v_ks_1441_; lean_object* v_vs_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1462_; 
v_ks_1441_ = lean_ctor_get(v_x_1390_, 0);
v_vs_1442_ = lean_ctor_get(v_x_1390_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1390_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1444_ = v_x_1390_;
v_isShared_1445_ = v_isSharedCheck_1462_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_vs_1442_);
lean_inc(v_ks_1441_);
lean_dec(v_x_1390_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1462_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_ks_1441_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_vs_1442_);
v___x_1447_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v_newNode_1448_; uint8_t v___y_1450_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_newNode_1448_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1447_, v_x_1393_, v_x_1394_);
v___x_1456_ = ((size_t)7ULL);
v___x_1457_ = lean_usize_dec_le(v___x_1456_, v_x_1392_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1448_);
v___x_1459_ = lean_unsigned_to_nat(4u);
v___x_1460_ = lean_nat_dec_lt(v___x_1458_, v___x_1459_);
lean_dec(v___x_1458_);
v___y_1450_ = v___x_1460_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1457_;
goto v___jp_1449_;
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
lean_object* v_ks_1451_; lean_object* v_vs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_ks_1451_ = lean_ctor_get(v_newNode_1448_, 0);
lean_inc_ref(v_ks_1451_);
v_vs_1452_ = lean_ctor_get(v_newNode_1448_, 1);
lean_inc_ref(v_vs_1452_);
lean_dec_ref(v_newNode_1448_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2);
v___x_1455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1392_, v_ks_1451_, v_vs_1452_, v___x_1453_, v___x_1454_);
lean_dec_ref(v_vs_1452_);
lean_dec_ref(v_ks_1451_);
return v___x_1455_;
}
else
{
return v_newNode_1448_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_i_1466_, lean_object* v_entries_1467_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = lean_array_get_size(v_keys_1464_);
v___x_1469_ = lean_nat_dec_lt(v_i_1466_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v_i_1466_);
return v_entries_1467_;
}
else
{
lean_object* v_k_1470_; lean_object* v_v_1471_; uint64_t v___x_1472_; size_t v_h_1473_; size_t v___x_1474_; lean_object* v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v_h_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_k_1470_ = lean_array_fget_borrowed(v_keys_1464_, v_i_1466_);
v_v_1471_ = lean_array_fget_borrowed(v_vals_1465_, v_i_1466_);
v___x_1472_ = l_Lean_instHashableFVarId_hash(v_k_1470_);
v_h_1473_ = lean_uint64_to_usize(v___x_1472_);
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_sub(v_depth_1463_, v___x_1476_);
v___x_1478_ = lean_usize_mul(v___x_1474_, v___x_1477_);
v_h_1479_ = lean_usize_shift_right(v_h_1473_, v___x_1478_);
v___x_1480_ = lean_nat_add(v_i_1466_, v___x_1475_);
lean_dec(v_i_1466_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
v___x_1481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1467_, v_h_1479_, v_depth_1463_, v_k_1470_, v_v_1471_);
v_i_1466_ = v___x_1480_;
v_entries_1467_ = v___x_1481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1483_, lean_object* v_keys_1484_, lean_object* v_vals_1485_, lean_object* v_i_1486_, lean_object* v_entries_1487_){
_start:
{
size_t v_depth_boxed_1488_; lean_object* v_res_1489_; 
v_depth_boxed_1488_ = lean_unbox_usize(v_depth_1483_);
lean_dec(v_depth_1483_);
v_res_1489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1488_, v_keys_1484_, v_vals_1485_, v_i_1486_, v_entries_1487_);
lean_dec_ref(v_vals_1485_);
lean_dec_ref(v_keys_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
size_t v_x_98761__boxed_1495_; size_t v_x_98762__boxed_1496_; lean_object* v_res_1497_; 
v_x_98761__boxed_1495_ = lean_unbox_usize(v_x_1491_);
lean_dec(v_x_1491_);
v_x_98762__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_res_1497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1490_, v_x_98761__boxed_1495_, v_x_98762__boxed_1496_, v_x_1493_, v_x_1494_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
uint64_t v___x_1501_; size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = l_Lean_instHashableFVarId_hash(v_x_1499_);
v___x_1502_ = lean_uint64_to_usize(v___x_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1498_, v___x_1502_, v___x_1503_, v_x_1499_, v_x_1500_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1505_, size_t v_i_1506_, size_t v_stop_1507_, lean_object* v_b_1508_){
_start:
{
lean_object* v___y_1510_; uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_eq(v_i_1506_, v_stop_1507_);
if (v___x_1514_ == 0)
{
lean_object* v_fvarIdToDecl_1515_; lean_object* v_decls_1516_; lean_object* v_auxDeclToFullName_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_fvarIdToDecl_1515_ = lean_ctor_get(v_b_1508_, 0);
v_decls_1516_ = lean_ctor_get(v_b_1508_, 1);
v_auxDeclToFullName_1517_ = lean_ctor_get(v_b_1508_, 2);
v___x_1518_ = lean_array_uget_borrowed(v_as_1505_, v_i_1506_);
v___x_1519_ = l_Lean_Expr_fvarId_x21(v___x_1518_);
lean_inc_ref(v_b_1508_);
v___x_1520_ = lean_local_ctx_find(v_b_1508_, v___x_1519_);
if (lean_obj_tag(v___x_1520_) == 0)
{
v___y_1510_ = v_b_1508_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1547_; 
lean_inc(v_auxDeclToFullName_1517_);
lean_inc_ref(v_decls_1516_);
lean_inc_ref(v_fvarIdToDecl_1515_);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_b_1508_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1548_ = lean_ctor_get(v_b_1508_, 2);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_b_1508_, 1);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_b_1508_, 0);
lean_dec(v_unused_1550_);
v___x_1522_ = v_b_1508_;
v_isShared_1523_ = v_isSharedCheck_1547_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v_b_1508_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1547_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_val_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1546_; 
v_val_1524_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1526_ = v___x_1520_;
v_isShared_1527_ = v_isSharedCheck_1546_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_val_1524_);
lean_dec(v___x_1520_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1546_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1542_; lean_object* v_fvarId_1545_; 
v___x_1528_ = l_Lean_LocalDecl_type(v_val_1524_);
v___x_1529_ = l_Lean_Expr_cleanupAnnotations(v___x_1528_);
v___x_1530_ = l_Lean_LocalDecl_setType(v_val_1524_, v___x_1529_);
v_fvarId_1545_ = lean_ctor_get(v___x_1530_, 1);
lean_inc(v_fvarId_1545_);
v___y_1542_ = v_fvarId_1545_;
goto v___jp_1541_;
v___jp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1530_);
v___x_1535_ = v___x_1526_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1530_);
v___x_1535_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = l_Lean_PersistentArray_set___redArg(v_decls_1516_, v___y_1533_, v___x_1535_);
lean_dec(v___y_1533_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1536_);
lean_ctor_set(v___x_1522_, 0, v___y_1532_);
v___x_1538_ = v___x_1522_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___y_1532_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_auxDeclToFullName_1517_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
v___y_1510_ = v___x_1538_;
goto v___jp_1509_;
}
}
}
v___jp_1541_:
{
lean_object* v___x_1543_; lean_object* v_index_1544_; 
lean_inc_ref(v___x_1530_);
v___x_1543_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1515_, v___y_1542_, v___x_1530_);
v_index_1544_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_index_1544_);
v___y_1532_ = v___x_1543_;
v___y_1533_ = v_index_1544_;
goto v___jp_1531_;
}
}
}
}
}
else
{
return v_b_1508_;
}
v___jp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1506_, v___x_1511_);
v_i_1506_ = v___x_1512_;
v_b_1508_ = v___y_1510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_stop_1553_, lean_object* v_b_1554_){
_start:
{
size_t v_i_boxed_1555_; size_t v_stop_boxed_1556_; lean_object* v_res_1557_; 
v_i_boxed_1555_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_stop_boxed_1556_ = lean_unbox_usize(v_stop_1553_);
lean_dec(v_stop_1553_);
v_res_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1551_, v_i_boxed_1555_, v_stop_boxed_1556_, v_b_1554_);
lean_dec_ref(v_as_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1558_, size_t v_i_1559_, lean_object* v_bs_1560_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_lt(v_i_1559_, v_sz_1558_);
if (v___x_1561_ == 0)
{
return v_bs_1560_;
}
else
{
lean_object* v_v_1562_; lean_object* v_snd_1563_; lean_object* v___x_1564_; lean_object* v_bs_x27_1565_; size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v_v_1562_ = lean_array_uget_borrowed(v_bs_1560_, v_i_1559_);
v_snd_1563_ = lean_ctor_get(v_v_1562_, 1);
lean_inc(v_snd_1563_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v_bs_x27_1565_ = lean_array_uset(v_bs_1560_, v_i_1559_, v___x_1564_);
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1559_, v___x_1566_);
v___x_1568_ = lean_array_uset(v_bs_x27_1565_, v_i_1559_, v_snd_1563_);
v_i_1559_ = v___x_1567_;
v_bs_1560_ = v___x_1568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1570_, lean_object* v_i_1571_, lean_object* v_bs_1572_){
_start:
{
size_t v_sz_boxed_1573_; size_t v_i_boxed_1574_; lean_object* v_res_1575_; 
v_sz_boxed_1573_ = lean_unbox_usize(v_sz_1570_);
lean_dec(v_sz_1570_);
v_i_boxed_1574_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1573_, v_i_boxed_1574_, v_bs_1572_);
return v_res_1575_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1587_, lean_object* v_value_1588_, uint8_t v___x_1589_, uint8_t v___x_1590_, lean_object* v___x_1591_, uint8_t v___y_1592_, lean_object* v_xs_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; 
lean_inc(v_type_1587_);
v___x_1601_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1601_, 0, v_type_1587_);
v___x_1602_ = 2;
v___x_1603_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1601_, v___x_1602_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___y_1609_; lean_object* v___y_1645_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v_sz_1605_ = lean_array_size(v_xs_1593_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1605_, v___x_1606_, v_xs_1593_);
if (v___y_1592_ == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1645_ = v___x_1681_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1645_ = v___x_1682_;
goto v___jp_1644_;
}
v___jp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; 
lean_inc(v_a_1604_);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_a_1604_);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_box(v___x_1589_);
v___x_1613_ = lean_box(v___x_1590_);
lean_inc_ref(v___x_1607_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1614_, 0, v_value_1588_);
lean_closure_set(v___f_1614_, 1, v___x_1610_);
lean_closure_set(v___f_1614_, 2, v___x_1612_);
lean_closure_set(v___f_1614_, 3, v___x_1611_);
lean_closure_set(v___f_1614_, 4, v___x_1607_);
lean_closure_set(v___f_1614_, 5, v___x_1613_);
v___x_1615_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1609_, v___f_1614_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = 1;
v___x_1618_ = l_Lean_Meta_mkForallFVars(v___x_1607_, v_a_1604_, v___x_1590_, v___x_1589_, v___x_1589_, v___x_1617_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec_ref(v___x_1607_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_a_1619_);
lean_ctor_set(v___x_1623_, 1, v_a_1616_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1616_);
v_a_1628_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1618_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1618_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v___x_1607_);
lean_dec(v_a_1604_);
v_a_1636_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1615_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1615_);
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
v___jp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1645_);
v___x_1647_ = l_Lean_stringToMessageData(v___y_1645_);
lean_inc_ref(v___x_1647_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
lean_inc(v_type_1587_);
v___x_1651_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1604_, v_type_1587_, v___x_1650_, v___y_1595_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec_ref(v___x_1651_);
v___x_1652_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1647_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1649_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_inc(v_a_1604_);
v___x_1656_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1604_, v_type_1587_, v___x_1655_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_lctx_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
lean_dec_ref(v___x_1656_);
v_lctx_1657_ = lean_ctor_get(v___y_1596_, 2);
v___x_1658_ = lean_array_get_size(v___x_1607_);
v___x_1659_ = lean_nat_dec_lt(v___x_1591_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_inc_ref(v_lctx_1657_);
v___y_1609_ = v_lctx_1657_;
goto v___jp_1608_;
}
else
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_le(v___x_1658_, v___x_1658_);
if (v___x_1660_ == 0)
{
if (v___x_1659_ == 0)
{
lean_inc_ref(v_lctx_1657_);
v___y_1609_ = v_lctx_1657_;
goto v___jp_1608_;
}
else
{
size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_usize_of_nat(v___x_1658_);
lean_inc_ref(v_lctx_1657_);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1607_, v___x_1606_, v___x_1661_, v_lctx_1657_);
v___y_1609_ = v___x_1662_;
goto v___jp_1608_;
}
}
else
{
size_t v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_usize_of_nat(v___x_1658_);
lean_inc_ref(v_lctx_1657_);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1607_, v___x_1606_, v___x_1663_, v_lctx_1657_);
v___y_1609_ = v___x_1664_;
goto v___jp_1608_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v___x_1607_);
lean_dec(v_a_1604_);
lean_dec(v_value_1588_);
v_a_1665_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1656_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1656_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v___x_1647_);
lean_dec_ref(v___x_1607_);
lean_dec(v_a_1604_);
lean_dec(v_value_1588_);
lean_dec(v_type_1587_);
v_a_1673_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1651_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1651_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_xs_1593_);
lean_dec(v_value_1588_);
lean_dec(v_type_1587_);
v_a_1683_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1603_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1603_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1691_, lean_object* v_value_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v___y_1696_, lean_object* v_xs_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v___x_99080__boxed_1705_; uint8_t v___x_99081__boxed_1706_; uint8_t v___y_99083__boxed_1707_; lean_object* v_res_1708_; 
v___x_99080__boxed_1705_ = lean_unbox(v___x_1693_);
v___x_99081__boxed_1706_ = lean_unbox(v___x_1694_);
v___y_99083__boxed_1707_ = lean_unbox(v___y_1696_);
v_res_1708_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1691_, v_value_1692_, v___x_99080__boxed_1705_, v___x_99081__boxed_1706_, v___x_1695_, v___y_99083__boxed_1707_, v_xs_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___x_1695_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1709_, lean_object* v_a_1710_, uint8_t v_zeta_1711_, uint8_t v___y_1712_, lean_object* v_x_1713_, uint8_t v_usedOnly_1714_, uint8_t v___x_1715_, uint8_t v___x_1716_, lean_object* v_snd_1717_, lean_object* v_h_x27_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
lean_inc_ref(v_h_x27_1718_);
v___x_1727_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1709_, v_h_x27_1718_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref(v___x_1727_);
v___x_1728_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1710_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1728_) == 0)
{
if (v_zeta_1711_ == 0)
{
if (v___y_1712_ == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v_snd_1717_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = lean_unsigned_to_nat(2u);
v___x_1731_ = lean_mk_empty_array_with_capacity(v___x_1730_);
v___x_1732_ = lean_array_push(v___x_1731_, v_x_1713_);
v___x_1733_ = lean_array_push(v___x_1732_, v_h_x27_1718_);
v___x_1734_ = 1;
v___x_1735_ = l_Lean_Meta_mkLetFVars(v___x_1733_, v_a_1729_, v_usedOnly_1714_, v___x_1715_, v___x_1734_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v___x_1733_);
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_a_1736_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1728_);
v___x_1737_ = lean_unsigned_to_nat(2u);
v___x_1738_ = lean_mk_empty_array_with_capacity(v___x_1737_);
v___x_1739_ = lean_array_push(v___x_1738_, v_x_1713_);
v___x_1740_ = lean_array_push(v___x_1739_, v_h_x27_1718_);
v___x_1741_ = 1;
v___x_1742_ = l_Lean_Meta_mkLambdaFVars(v___x_1740_, v_a_1736_, v___x_1715_, v___x_1716_, v___x_1715_, v___x_1716_, v___x_1741_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v___x_1740_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
lean_inc_ref(v_snd_1717_);
v___x_1744_ = l_Lean_Meta_mkEqRefl(v_snd_1717_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1753_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = l_Lean_mkAppB(v_a_1743_, v_snd_1717_, v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
else
{
lean_dec(v_a_1743_);
lean_dec_ref(v_snd_1717_);
return v___x_1744_;
}
}
else
{
lean_dec_ref(v_snd_1717_);
return v___x_1742_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_a_1754_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1728_);
v___x_1755_ = lean_unsigned_to_nat(2u);
v___x_1756_ = lean_mk_empty_array_with_capacity(v___x_1755_);
lean_inc_ref(v___x_1756_);
v___x_1757_ = lean_array_push(v___x_1756_, v_x_1713_);
v___x_1758_ = lean_array_push(v___x_1757_, v_h_x27_1718_);
v___x_1759_ = l_Lean_Expr_abstractM(v_a_1754_, v___x_1758_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v___x_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
lean_inc_ref(v_snd_1717_);
v___x_1761_ = l_Lean_Meta_mkEqRefl(v_snd_1717_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1772_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1766_ = lean_array_push(v___x_1756_, v_snd_1717_);
v___x_1767_ = lean_array_push(v___x_1766_, v_a_1762_);
v___x_1768_ = lean_expr_instantiate_rev(v_a_1760_, v___x_1767_);
lean_dec_ref(v___x_1767_);
lean_dec(v_a_1760_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1770_ = v___x_1764_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_dec(v_a_1760_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_snd_1717_);
return v___x_1761_;
}
}
else
{
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_snd_1717_);
return v___x_1759_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1718_);
lean_dec_ref(v_snd_1717_);
lean_dec_ref(v_x_1713_);
return v___x_1728_;
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_h_x27_1718_);
lean_dec_ref(v_snd_1717_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v_a_1710_);
v_a_1773_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1727_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1727_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1781_ = _args[0];
lean_object* v_a_1782_ = _args[1];
lean_object* v_zeta_1783_ = _args[2];
lean_object* v___y_1784_ = _args[3];
lean_object* v_x_1785_ = _args[4];
lean_object* v_usedOnly_1786_ = _args[5];
lean_object* v___x_1787_ = _args[6];
lean_object* v___x_1788_ = _args[7];
lean_object* v_snd_1789_ = _args[8];
lean_object* v_h_x27_1790_ = _args[9];
lean_object* v___y_1791_ = _args[10];
lean_object* v___y_1792_ = _args[11];
lean_object* v___y_1793_ = _args[12];
lean_object* v___y_1794_ = _args[13];
lean_object* v___y_1795_ = _args[14];
lean_object* v___y_1796_ = _args[15];
lean_object* v___y_1797_ = _args[16];
lean_object* v___y_1798_ = _args[17];
_start:
{
uint8_t v_zeta_boxed_1799_; uint8_t v___y_99307__boxed_1800_; uint8_t v_usedOnly_boxed_1801_; uint8_t v___x_99308__boxed_1802_; uint8_t v___x_99309__boxed_1803_; lean_object* v_res_1804_; 
v_zeta_boxed_1799_ = lean_unbox(v_zeta_1783_);
v___y_99307__boxed_1800_ = lean_unbox(v___y_1784_);
v_usedOnly_boxed_1801_ = lean_unbox(v_usedOnly_1786_);
v___x_99308__boxed_1802_ = lean_unbox(v___x_1787_);
v___x_99309__boxed_1803_ = lean_unbox(v___x_1788_);
v_res_1804_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1781_, v_a_1782_, v_zeta_boxed_1799_, v___y_99307__boxed_1800_, v_x_1785_, v_usedOnly_boxed_1801_, v___x_99308__boxed_1802_, v___x_99309__boxed_1803_, v_snd_1789_, v_h_x27_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1805_, lean_object* v_a_1806_, uint8_t v_zeta_1807_, lean_object* v_x_1808_, uint8_t v_usedOnly_1809_, uint8_t v___x_1810_, lean_object* v_snd_1811_, uint8_t v___y_1812_, uint8_t v___x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1805_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1806_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
if (v_zeta_1807_ == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_snd_1811_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_unsigned_to_nat(1u);
v___x_1825_ = lean_mk_empty_array_with_capacity(v___x_1824_);
v___x_1826_ = lean_array_push(v___x_1825_, v_x_1808_);
v___x_1827_ = 1;
v___x_1828_ = l_Lean_Meta_mkLetFVars(v___x_1826_, v_a_1823_, v_usedOnly_1809_, v___x_1810_, v___x_1827_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec_ref(v___x_1826_);
return v___x_1828_;
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1829_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1822_);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_mk_empty_array_with_capacity(v___x_1830_);
v___x_1832_ = lean_array_push(v___x_1831_, v_x_1808_);
v___x_1833_ = l_Lean_Expr_abstractM(v_a_1829_, v___x_1832_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec_ref(v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_expr_instantiate1(v_a_1834_, v_snd_1811_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_dec_ref(v_snd_1811_);
return v___x_1833_;
}
}
}
else
{
lean_dec_ref(v_snd_1811_);
lean_dec_ref(v_x_1808_);
return v___x_1822_;
}
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1844_; 
v_val_1843_ = lean_ctor_get(v_eq_x3f_1805_, 0);
lean_inc(v_val_1843_);
lean_dec_ref(v_eq_x3f_1805_);
lean_inc_ref(v_snd_1811_);
lean_inc_ref(v_x_1808_);
v___x_1844_ = l_Lean_Meta_mkEq(v_x_1808_, v_snd_1811_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
lean_inc_ref(v_x_1808_);
v___x_1846_ = l_Lean_Meta_mkEqRefl(v_x_1808_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = lean_box(v_zeta_1807_);
v___x_1849_ = lean_box(v___y_1812_);
v___x_1850_ = lean_box(v_usedOnly_1809_);
v___x_1851_ = lean_box(v___x_1810_);
v___x_1852_ = lean_box(v___x_1813_);
lean_inc(v_val_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1853_, 0, v_val_1843_);
lean_closure_set(v___f_1853_, 1, v_a_1806_);
lean_closure_set(v___f_1853_, 2, v___x_1848_);
lean_closure_set(v___f_1853_, 3, v___x_1849_);
lean_closure_set(v___f_1853_, 4, v_x_1808_);
lean_closure_set(v___f_1853_, 5, v___x_1850_);
lean_closure_set(v___f_1853_, 6, v___x_1851_);
lean_closure_set(v___f_1853_, 7, v___x_1852_);
lean_closure_set(v___f_1853_, 8, v_snd_1811_);
v___x_1854_ = l_Lean_TSyntax_getId(v_val_1843_);
lean_dec(v_val_1843_);
v___x_1855_ = 0;
v___x_1856_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1854_, v_a_1845_, v_a_1847_, v___f_1853_, v___x_1813_, v___x_1855_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1856_;
}
else
{
lean_dec(v_a_1845_);
lean_dec(v_val_1843_);
lean_dec_ref(v_snd_1811_);
lean_dec_ref(v_x_1808_);
lean_dec_ref(v_a_1806_);
return v___x_1846_;
}
}
else
{
lean_dec(v_val_1843_);
lean_dec_ref(v_snd_1811_);
lean_dec_ref(v_x_1808_);
lean_dec_ref(v_a_1806_);
return v___x_1844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_eq_x3f_1857_ = _args[0];
lean_object* v_a_1858_ = _args[1];
lean_object* v_zeta_1859_ = _args[2];
lean_object* v_x_1860_ = _args[3];
lean_object* v_usedOnly_1861_ = _args[4];
lean_object* v___x_1862_ = _args[5];
lean_object* v_snd_1863_ = _args[6];
lean_object* v___y_1864_ = _args[7];
lean_object* v___x_1865_ = _args[8];
lean_object* v___y_1866_ = _args[9];
lean_object* v___y_1867_ = _args[10];
lean_object* v___y_1868_ = _args[11];
lean_object* v___y_1869_ = _args[12];
lean_object* v___y_1870_ = _args[13];
lean_object* v___y_1871_ = _args[14];
lean_object* v___y_1872_ = _args[15];
lean_object* v___y_1873_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1874_; uint8_t v_usedOnly_boxed_1875_; uint8_t v___x_99462__boxed_1876_; uint8_t v___y_99464__boxed_1877_; uint8_t v___x_99465__boxed_1878_; lean_object* v_res_1879_; 
v_zeta_boxed_1874_ = lean_unbox(v_zeta_1859_);
v_usedOnly_boxed_1875_ = lean_unbox(v_usedOnly_1861_);
v___x_99462__boxed_1876_ = lean_unbox(v___x_1862_);
v___y_99464__boxed_1877_ = lean_unbox(v___y_1864_);
v___x_99465__boxed_1878_ = lean_unbox(v___x_1865_);
v_res_1879_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1857_, v_a_1858_, v_zeta_boxed_1874_, v_x_1860_, v_usedOnly_boxed_1875_, v___x_99462__boxed_1876_, v_snd_1863_, v___y_99464__boxed_1877_, v___x_99465__boxed_1878_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1880_, lean_object* v_eq_x3f_1881_, lean_object* v_a_1882_, uint8_t v_zeta_1883_, uint8_t v_usedOnly_1884_, uint8_t v___x_1885_, lean_object* v_snd_1886_, uint8_t v___y_1887_, uint8_t v___x_1888_, lean_object* v_letOrReassign_1889_, lean_object* v_a_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
lean_inc_ref(v_x_1891_);
v___x_1900_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1880_, v_x_1891_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___y_1906_; lean_object* v___x_1907_; 
lean_dec_ref(v___x_1900_);
v___x_1901_ = lean_box(v_zeta_1883_);
v___x_1902_ = lean_box(v_usedOnly_1884_);
v___x_1903_ = lean_box(v___x_1885_);
v___x_1904_ = lean_box(v___y_1887_);
v___x_1905_ = lean_box(v___x_1888_);
v___y_1906_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 17, 9);
lean_closure_set(v___y_1906_, 0, v_eq_x3f_1881_);
lean_closure_set(v___y_1906_, 1, v_a_1882_);
lean_closure_set(v___y_1906_, 2, v___x_1901_);
lean_closure_set(v___y_1906_, 3, v_x_1891_);
lean_closure_set(v___y_1906_, 4, v___x_1902_);
lean_closure_set(v___y_1906_, 5, v___x_1903_);
lean_closure_set(v___y_1906_, 6, v_snd_1886_);
lean_closure_set(v___y_1906_, 7, v___x_1904_);
lean_closure_set(v___y_1906_, 8, v___x_1905_);
v___x_1907_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1889_, v_a_1890_, v___y_1906_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1907_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_x_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_letOrReassign_1889_);
lean_dec_ref(v_snd_1886_);
lean_dec_ref(v_a_1882_);
lean_dec(v_eq_x3f_1881_);
v_a_1908_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1900_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1900_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1916_ = _args[0];
lean_object* v_eq_x3f_1917_ = _args[1];
lean_object* v_a_1918_ = _args[2];
lean_object* v_zeta_1919_ = _args[3];
lean_object* v_usedOnly_1920_ = _args[4];
lean_object* v___x_1921_ = _args[5];
lean_object* v_snd_1922_ = _args[6];
lean_object* v___y_1923_ = _args[7];
lean_object* v___x_1924_ = _args[8];
lean_object* v_letOrReassign_1925_ = _args[9];
lean_object* v_a_1926_ = _args[10];
lean_object* v_x_1927_ = _args[11];
lean_object* v___y_1928_ = _args[12];
lean_object* v___y_1929_ = _args[13];
lean_object* v___y_1930_ = _args[14];
lean_object* v___y_1931_ = _args[15];
lean_object* v___y_1932_ = _args[16];
lean_object* v___y_1933_ = _args[17];
lean_object* v___y_1934_ = _args[18];
lean_object* v___y_1935_ = _args[19];
_start:
{
uint8_t v_zeta_boxed_1936_; uint8_t v_usedOnly_boxed_1937_; uint8_t v___x_99575__boxed_1938_; uint8_t v___y_99577__boxed_1939_; uint8_t v___x_99578__boxed_1940_; lean_object* v_res_1941_; 
v_zeta_boxed_1936_ = lean_unbox(v_zeta_1919_);
v_usedOnly_boxed_1937_ = lean_unbox(v_usedOnly_1920_);
v___x_99575__boxed_1938_ = lean_unbox(v___x_1921_);
v___y_99577__boxed_1939_ = lean_unbox(v___y_1923_);
v___x_99578__boxed_1940_ = lean_unbox(v___x_1924_);
v_res_1941_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1916_, v_eq_x3f_1917_, v_a_1918_, v_zeta_boxed_1936_, v_usedOnly_boxed_1937_, v___x_99575__boxed_1938_, v_snd_1922_, v___y_99577__boxed_1939_, v___x_99578__boxed_1940_, v_letOrReassign_1925_, v_a_1926_, v_x_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1942_, lean_object* v_____do__lift_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1943_, v___x_1942_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1954_, lean_object* v_____do__lift_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v___x_99649__boxed_1964_; lean_object* v_res_1965_; 
v___x_99649__boxed_1964_ = lean_unbox(v___x_1954_);
v_res_1965_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99649__boxed_1964_, v_____do__lift_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v_____do__lift_1955_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1966_, lean_object* v___x_1967_, uint8_t v___x_1968_, lean_object* v___x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1966_, v___x_1967_, v___x_1968_, v___x_1968_, v___x_1969_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1979_, lean_object* v___x_1980_, lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v___x_99684__boxed_1991_; lean_object* v_res_1992_; 
v___x_99684__boxed_1991_ = lean_unbox(v___x_1981_);
v_res_1992_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1979_, v___x_1980_, v___x_99684__boxed_1991_, v___x_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
lean_inc_ref(v___y_1994_);
v___x_2002_ = lean_apply_8(v_x_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, lean_box(0));
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec_ref(v___y_2004_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_2013_, lean_object* v_mkInfoTree_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v_a_2020_, lean_object* v_a_x3f_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_infoState_2024_; lean_object* v_trees_2025_; lean_object* v___x_2026_; 
v___x_2023_ = lean_st_ref_get(v___y_2013_);
v_infoState_2024_ = lean_ctor_get(v___x_2023_, 7);
lean_inc_ref(v_infoState_2024_);
lean_dec(v___x_2023_);
v_trees_2025_ = lean_ctor_get(v_infoState_2024_, 2);
lean_inc_ref(v_trees_2025_);
lean_dec_ref(v_infoState_2024_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
v___x_2026_ = lean_apply_8(v_mkInfoTree_2014_, v_trees_2025_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2013_, lean_box(0));
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2065_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2065_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2065_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v_infoState_2032_; lean_object* v_env_2033_; lean_object* v_nextMacroScope_2034_; lean_object* v_ngen_2035_; lean_object* v_auxDeclNGen_2036_; lean_object* v_traceState_2037_; lean_object* v_cache_2038_; lean_object* v_messages_2039_; lean_object* v_snapshotTasks_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2064_; 
v___x_2031_ = lean_st_ref_take(v___y_2013_);
v_infoState_2032_ = lean_ctor_get(v___x_2031_, 7);
v_env_2033_ = lean_ctor_get(v___x_2031_, 0);
v_nextMacroScope_2034_ = lean_ctor_get(v___x_2031_, 1);
v_ngen_2035_ = lean_ctor_get(v___x_2031_, 2);
v_auxDeclNGen_2036_ = lean_ctor_get(v___x_2031_, 3);
v_traceState_2037_ = lean_ctor_get(v___x_2031_, 4);
v_cache_2038_ = lean_ctor_get(v___x_2031_, 5);
v_messages_2039_ = lean_ctor_get(v___x_2031_, 6);
v_snapshotTasks_2040_ = lean_ctor_get(v___x_2031_, 8);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2042_ = v___x_2031_;
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snapshotTasks_2040_);
lean_inc(v_infoState_2032_);
lean_inc(v_messages_2039_);
lean_inc(v_cache_2038_);
lean_inc(v_traceState_2037_);
lean_inc(v_auxDeclNGen_2036_);
lean_inc(v_ngen_2035_);
lean_inc(v_nextMacroScope_2034_);
lean_inc(v_env_2033_);
lean_dec(v___x_2031_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2064_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v_enabled_2044_; lean_object* v_assignment_2045_; lean_object* v_lazyAssignment_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2062_; 
v_enabled_2044_ = lean_ctor_get_uint8(v_infoState_2032_, sizeof(void*)*3);
v_assignment_2045_ = lean_ctor_get(v_infoState_2032_, 0);
v_lazyAssignment_2046_ = lean_ctor_get(v_infoState_2032_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_infoState_2032_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_infoState_2032_, 2);
lean_dec(v_unused_2063_);
v___x_2048_ = v_infoState_2032_;
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_lazyAssignment_2046_);
lean_inc(v_assignment_2045_);
lean_dec(v_infoState_2032_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = l_Lean_PersistentArray_push___redArg(v_a_2020_, v_a_2027_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 2, v___x_2050_);
v___x_2052_ = v___x_2048_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_assignment_2045_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_lazyAssignment_2046_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v___x_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2061_, sizeof(void*)*3, v_enabled_2044_);
v___x_2052_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 7, v___x_2052_);
v___x_2054_ = v___x_2042_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_env_2033_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_nextMacroScope_2034_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_ngen_2035_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_auxDeclNGen_2036_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_traceState_2037_);
lean_ctor_set(v_reuseFailAlloc_2060_, 5, v_cache_2038_);
lean_ctor_set(v_reuseFailAlloc_2060_, 6, v_messages_2039_);
lean_ctor_set(v_reuseFailAlloc_2060_, 7, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2060_, 8, v_snapshotTasks_2040_);
v___x_2054_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_st_ref_set(v___y_2013_, v___x_2054_);
v___x_2056_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2056_);
v___x_2058_ = v___x_2029_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_a_2020_);
v_a_2066_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2026_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2026_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_2074_, lean_object* v_mkInfoTree_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v_a_2081_, lean_object* v_a_x3f_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2074_, v_mkInfoTree_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v_a_2081_, v_a_x3f_2082_);
lean_dec(v_a_x3f_2082_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2074_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v_infoState_2088_; lean_object* v_trees_2089_; lean_object* v___x_2090_; lean_object* v_infoState_2091_; lean_object* v_env_2092_; lean_object* v_nextMacroScope_2093_; lean_object* v_ngen_2094_; lean_object* v_auxDeclNGen_2095_; lean_object* v_traceState_2096_; lean_object* v_cache_2097_; lean_object* v_messages_2098_; lean_object* v_snapshotTasks_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2122_; 
v___x_2087_ = lean_st_ref_get(v___y_2085_);
v_infoState_2088_ = lean_ctor_get(v___x_2087_, 7);
lean_inc_ref(v_infoState_2088_);
lean_dec(v___x_2087_);
v_trees_2089_ = lean_ctor_get(v_infoState_2088_, 2);
lean_inc_ref(v_trees_2089_);
lean_dec_ref(v_infoState_2088_);
v___x_2090_ = lean_st_ref_take(v___y_2085_);
v_infoState_2091_ = lean_ctor_get(v___x_2090_, 7);
v_env_2092_ = lean_ctor_get(v___x_2090_, 0);
v_nextMacroScope_2093_ = lean_ctor_get(v___x_2090_, 1);
v_ngen_2094_ = lean_ctor_get(v___x_2090_, 2);
v_auxDeclNGen_2095_ = lean_ctor_get(v___x_2090_, 3);
v_traceState_2096_ = lean_ctor_get(v___x_2090_, 4);
v_cache_2097_ = lean_ctor_get(v___x_2090_, 5);
v_messages_2098_ = lean_ctor_get(v___x_2090_, 6);
v_snapshotTasks_2099_ = lean_ctor_get(v___x_2090_, 8);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2101_ = v___x_2090_;
v_isShared_2102_ = v_isSharedCheck_2122_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snapshotTasks_2099_);
lean_inc(v_infoState_2091_);
lean_inc(v_messages_2098_);
lean_inc(v_cache_2097_);
lean_inc(v_traceState_2096_);
lean_inc(v_auxDeclNGen_2095_);
lean_inc(v_ngen_2094_);
lean_inc(v_nextMacroScope_2093_);
lean_inc(v_env_2092_);
lean_dec(v___x_2090_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2122_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint8_t v_enabled_2103_; lean_object* v_assignment_2104_; lean_object* v_lazyAssignment_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2120_; 
v_enabled_2103_ = lean_ctor_get_uint8(v_infoState_2091_, sizeof(void*)*3);
v_assignment_2104_ = lean_ctor_get(v_infoState_2091_, 0);
v_lazyAssignment_2105_ = lean_ctor_get(v_infoState_2091_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_infoState_2091_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_infoState_2091_, 2);
lean_dec(v_unused_2121_);
v___x_2107_ = v_infoState_2091_;
v_isShared_2108_ = v_isSharedCheck_2120_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_lazyAssignment_2105_);
lean_inc(v_assignment_2104_);
lean_dec(v_infoState_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2120_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2109_ = lean_unsigned_to_nat(32u);
v___x_2110_ = lean_mk_empty_array_with_capacity(v___x_2109_);
lean_dec_ref(v___x_2110_);
v___x_2111_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 2, v___x_2111_);
v___x_2113_ = v___x_2107_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_assignment_2104_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_lazyAssignment_2105_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v___x_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2119_, sizeof(void*)*3, v_enabled_2103_);
v___x_2113_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 7, v___x_2113_);
v___x_2115_ = v___x_2101_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_env_2092_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_nextMacroScope_2093_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_ngen_2094_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_auxDeclNGen_2095_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_traceState_2096_);
lean_ctor_set(v_reuseFailAlloc_2118_, 5, v_cache_2097_);
lean_ctor_set(v_reuseFailAlloc_2118_, 6, v_messages_2098_);
lean_ctor_set(v_reuseFailAlloc_2118_, 7, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2118_, 8, v_snapshotTasks_2099_);
v___x_2115_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_st_ref_set(v___y_2085_, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_trees_2089_);
return v___x_2117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2123_);
lean_dec(v___y_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_2126_, lean_object* v_mkInfoTree_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v_infoState_2136_; uint8_t v_enabled_2137_; 
v___x_2135_ = lean_st_ref_get(v___y_2133_);
v_infoState_2136_ = lean_ctor_get(v___x_2135_, 7);
lean_inc_ref(v_infoState_2136_);
lean_dec(v___x_2135_);
v_enabled_2137_ = lean_ctor_get_uint8(v_infoState_2136_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2136_);
if (v_enabled_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v_mkInfoTree_2127_);
lean_inc(v___y_2133_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v___y_2129_);
lean_inc_ref(v___y_2128_);
v___x_2138_ = lean_apply_7(v_x_2126_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, lean_box(0));
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v_r_2141_; 
v___x_2139_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2133_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
lean_inc(v___y_2133_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v___y_2129_);
lean_inc_ref(v___y_2128_);
v_r_2141_ = lean_apply_7(v_x_2126_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, lean_box(0));
if (lean_obj_tag(v_r_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2166_; 
v_a_2142_ = lean_ctor_get(v_r_2141_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_r_2141_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2144_ = v_r_2141_;
v_isShared_2145_ = v_isSharedCheck_2166_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v_r_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2166_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
lean_inc(v_a_2142_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 1);
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2133_, v_mkInfoTree_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v_a_2140_, v___x_2147_);
lean_dec_ref(v___x_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2156_);
v___x_2150_ = v___x_2148_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v___x_2148_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v_a_2142_);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2142_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_2142_);
v_a_2157_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2148_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2148_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v_r_2141_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v_r_2141_);
v___x_2168_ = lean_box(0);
v___x_2169_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2133_, v_mkInfoTree_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v_a_2140_, v___x_2168_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v___x_2169_, 0);
lean_dec(v_unused_2177_);
v___x_2171_ = v___x_2169_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_dec(v___x_2169_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 1);
lean_ctor_set(v___x_2171_, 0, v_a_2167_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2167_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2167_);
v_a_2178_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2169_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2169_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_2186_, lean_object* v_mkInfoTree_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2186_, v_mkInfoTree_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2196_, lean_object* v_output_2197_, lean_object* v_trees_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_lctx_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_lctx_2206_ = lean_ctor_get(v___y_2201_, 2);
lean_inc_ref(v_lctx_2206_);
v___x_2207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2207_, 0, v_lctx_2206_);
lean_ctor_set(v___x_2207_, 1, v_stx_2196_);
lean_ctor_set(v___x_2207_, 2, v_output_2197_);
v___x_2208_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v_trees_2198_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2211_, lean_object* v_output_2212_, lean_object* v_trees_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2211_, v_output_2212_, v_trees_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2222_, lean_object* v_output_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___f_2232_; lean_object* v___x_2233_; 
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2232_, 0, v_stx_2222_);
lean_closure_set(v___f_2232_, 1, v_output_2223_);
v___x_2233_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2224_, v___f_2232_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2234_, lean_object* v_output_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2234_, v_output_2235_, v_x_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2245_, lean_object* v_afterStx_2246_, lean_object* v_x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___f_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_inc_ref(v___y_2248_);
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2256_, 0, v_x_2247_);
lean_closure_set(v___f_2256_, 1, v___y_2248_);
lean_inc(v_afterStx_2246_);
lean_inc(v_beforeStx_2245_);
v___x_2257_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2257_, 0, lean_box(0));
lean_closure_set(v___x_2257_, 1, v_beforeStx_2245_);
lean_closure_set(v___x_2257_, 2, v_afterStx_2246_);
lean_closure_set(v___x_2257_, 3, v___f_2256_);
v___x_2258_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2245_, v_afterStx_2246_, v___x_2257_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2258_) == 0)
{
return v___x_2258_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2267_, lean_object* v_afterStx_2268_, lean_object* v_x_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2267_, v_afterStx_2268_, v_x_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2278_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2282_ = l_String_toRawSubstring_x27(v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2304_, uint8_t v___x_2305_, lean_object* v_config_2306_, lean_object* v_a_2307_, uint8_t v___x_2308_, lean_object* v___x_2309_, lean_object* v___x_2310_, lean_object* v___x_2311_, lean_object* v___f_2312_, lean_object* v___x_2313_, lean_object* v_body_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_term_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v_ref_2331_; lean_object* v___y_2332_; lean_object* v_ref_2338_; lean_object* v_quotContext_2339_; lean_object* v_currMacroScope_2340_; lean_object* v_ref_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v_eq_x3f_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_ref_2338_ = lean_ctor_get(v___y_2320_, 5);
v_quotContext_2339_ = lean_ctor_get(v___y_2320_, 10);
v_currMacroScope_2340_ = lean_ctor_get(v___y_2320_, 11);
v_ref_2341_ = l_Lean_replaceRef(v_rhs_2304_, v_ref_2338_);
v___x_2342_ = l_Lean_SourceInfo_fromRef(v_ref_2341_, v___x_2305_);
lean_dec(v_ref_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2342_, 2);
v___x_2344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2346_ = lean_ctor_get(v_config_2306_, 0);
lean_inc(v_eq_x3f_2346_);
lean_dec_ref(v_config_2306_);
v___x_2347_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2340_);
lean_inc(v_quotContext_2339_);
v___x_2348_ = l_Lean_addMacroScope(v_quotContext_2339_, v___x_2347_, v_currMacroScope_2340_);
v___x_2349_ = lean_box(0);
lean_inc(v___x_2348_);
v___x_2350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2342_);
lean_ctor_set(v___x_2350_, 1, v___x_2345_);
lean_ctor_set(v___x_2350_, 2, v___x_2348_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2311_);
lean_inc_ref(v___x_2310_);
lean_inc_ref(v___x_2309_);
v___x_2352_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2351_);
v___x_2353_ = l_Lean_Syntax_node2(v___x_2342_, v___x_2352_, v___x_2344_, v___x_2350_);
if (lean_obj_tag(v_eq_x3f_2346_) == 1)
{
lean_object* v_val_2354_; lean_object* v___x_2355_; 
v_val_2354_ = lean_ctor_get(v_eq_x3f_2346_, 0);
lean_inc(v_val_2354_);
lean_dec_ref(v_eq_x3f_2346_);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v_ref_2338_);
v___x_2355_ = lean_apply_9(v___f_2312_, v_ref_2338_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, lean_box(0));
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc_n(v_a_2356_, 23);
lean_dec_ref(v___x_2355_);
v___x_2357_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2311_, 5);
lean_inc_ref_n(v___x_2310_, 5);
lean_inc_ref_n(v___x_2309_, 5);
v___x_2358_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_a_2356_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_a_2356_);
lean_ctor_set(v___x_2361_, 1, v___x_2343_);
v___x_2362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2362_, 0, v_a_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2345_);
lean_ctor_set(v___x_2362_, 2, v___x_2348_);
lean_ctor_set(v___x_2362_, 3, v___x_2349_);
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2356_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2356_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2368_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_a_2356_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2372_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_a_2356_);
lean_ctor_set(v___x_2373_, 1, v___x_2371_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2375_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2376_, 0, v_a_2356_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
lean_ctor_set(v___x_2376_, 2, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2378_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_a_2356_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node2(v_a_2356_, v___x_2374_, v_val_2354_, v___x_2380_);
v___x_2382_ = l_Lean_Syntax_node2(v_a_2356_, v___x_2378_, v___x_2381_, v___x_2353_);
v___x_2383_ = l_Lean_Syntax_node1(v_a_2356_, v___x_2374_, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_a_2356_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2387_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2389_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2388_);
v___x_2390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_a_2356_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = l_Lean_Syntax_node1(v_a_2356_, v___x_2374_, v___x_2313_);
v___x_2393_ = l_Lean_Syntax_node1(v_a_2356_, v___x_2374_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_a_2356_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node4(v_a_2356_, v___x_2389_, v___x_2391_, v___x_2393_, v___x_2395_, v_body_2314_);
v___x_2397_ = l_Lean_Syntax_node1(v_a_2356_, v___x_2374_, v___x_2396_);
v___x_2398_ = l_Lean_Syntax_node1(v_a_2356_, v___x_2387_, v___x_2397_);
lean_inc_ref(v___x_2376_);
v___x_2399_ = l_Lean_Syntax_node6(v_a_2356_, v___x_2372_, v___x_2373_, v___x_2376_, v___x_2376_, v___x_2383_, v___x_2385_, v___x_2398_);
lean_inc_ref(v___x_2366_);
lean_inc_ref(v___x_2362_);
lean_inc_ref(v___x_2361_);
v___x_2400_ = l_Lean_Syntax_node5(v_a_2356_, v___x_2368_, v___x_2370_, v___x_2361_, v___x_2362_, v___x_2366_, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node7(v_a_2356_, v___x_2358_, v___x_2360_, v___x_2361_, v___x_2362_, v___x_2364_, v_rhs_2304_, v___x_2366_, v___x_2400_);
lean_inc(v_ref_2338_);
v_term_2324_ = v___x_2401_;
v___y_2325_ = v___y_2315_;
v___y_2326_ = v___y_2316_;
v___y_2327_ = v___y_2317_;
v___y_2328_ = v___y_2318_;
v___y_2329_ = v___y_2319_;
v___y_2330_ = v___y_2320_;
v_ref_2331_ = v_ref_2338_;
v___y_2332_ = v___y_2321_;
goto v___jp_2323_;
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_val_2354_);
lean_dec(v___x_2353_);
lean_dec(v___x_2348_);
lean_dec(v_body_2314_);
lean_dec(v___x_2313_);
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2310_);
lean_dec_ref(v___x_2309_);
lean_dec_ref(v_a_2307_);
lean_dec(v_rhs_2304_);
v_a_2402_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2355_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2355_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v___x_2410_; 
lean_dec(v_eq_x3f_2346_);
lean_inc_ref(v_a_2307_);
v___x_2410_ = l_Lean_Elab_Term_exprToSyntax(v_a_2307_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v_ref_2338_);
v___x_2412_ = lean_apply_9(v___f_2312_, v_ref_2338_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, lean_box(0));
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_n(v_a_2413_, 32);
lean_dec_ref(v___x_2412_);
v___x_2414_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2311_, 8);
lean_inc_ref_n(v___x_2310_, 8);
lean_inc_ref_n(v___x_2309_, 8);
v___x_2415_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2414_);
v___x_2416_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2417_, 0, v_a_2413_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_a_2413_);
lean_ctor_set(v___x_2418_, 1, v___x_2343_);
v___x_2419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2419_, 0, v_a_2413_);
lean_ctor_set(v___x_2419_, 1, v___x_2345_);
lean_ctor_set(v___x_2419_, 2, v___x_2348_);
lean_ctor_set(v___x_2419_, 3, v___x_2349_);
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2413_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_a_2413_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2425_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2424_);
v___x_2426_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_a_2413_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2429_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2413_);
lean_ctor_set(v___x_2430_, 1, v___x_2428_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2432_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2413_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
lean_ctor_set(v___x_2433_, 2, v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2435_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2434_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v_a_2413_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2413_);
lean_ctor_set(v___x_2438_, 1, v___x_2434_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2440_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2413_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2444_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2413_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2444_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2447_);
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_a_2413_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
lean_inc_ref_n(v___x_2433_, 2);
v___x_2451_ = l_Lean_Syntax_node5(v_a_2413_, v___x_2440_, v___x_2442_, v___x_2448_, v___x_2433_, v___x_2450_, v_a_2411_);
v___x_2452_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2413_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_inc_ref(v___x_2421_);
v___x_2454_ = l_Lean_Syntax_node5(v_a_2413_, v___x_2435_, v___x_2437_, v___x_2438_, v___x_2421_, v___x_2451_, v___x_2453_);
v___x_2455_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2454_);
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2457_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node2(v_a_2413_, v___x_2457_, v___x_2433_, v___x_2353_);
v___x_2459_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_a_2413_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2463_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2465_ = l_Lean_Name_mkStr4(v___x_2309_, v___x_2310_, v___x_2311_, v___x_2464_);
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2413_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2313_);
v___x_2469_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2413_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = l_Lean_Syntax_node4(v_a_2413_, v___x_2465_, v___x_2467_, v___x_2469_, v___x_2471_, v_body_2314_);
v___x_2473_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2431_, v___x_2472_);
v___x_2474_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2463_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node6(v_a_2413_, v___x_2429_, v___x_2430_, v___x_2433_, v___x_2455_, v___x_2459_, v___x_2461_, v___x_2474_);
lean_inc_ref(v___x_2423_);
lean_inc_ref(v___x_2419_);
lean_inc_ref(v___x_2418_);
v___x_2476_ = l_Lean_Syntax_node5(v_a_2413_, v___x_2425_, v___x_2427_, v___x_2418_, v___x_2419_, v___x_2423_, v___x_2475_);
v___x_2477_ = l_Lean_Syntax_node7(v_a_2413_, v___x_2415_, v___x_2417_, v___x_2418_, v___x_2419_, v___x_2421_, v_rhs_2304_, v___x_2423_, v___x_2476_);
lean_inc(v_ref_2338_);
v_term_2324_ = v___x_2477_;
v___y_2325_ = v___y_2315_;
v___y_2326_ = v___y_2316_;
v___y_2327_ = v___y_2317_;
v___y_2328_ = v___y_2318_;
v___y_2329_ = v___y_2319_;
v___y_2330_ = v___y_2320_;
v_ref_2331_ = v_ref_2338_;
v___y_2332_ = v___y_2321_;
goto v___jp_2323_;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2411_);
lean_dec(v___x_2353_);
lean_dec(v___x_2348_);
lean_dec(v_body_2314_);
lean_dec(v___x_2313_);
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2310_);
lean_dec_ref(v___x_2309_);
lean_dec_ref(v_a_2307_);
lean_dec(v_rhs_2304_);
v_a_2478_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2412_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2412_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v___x_2353_);
lean_dec(v___x_2348_);
lean_dec(v_body_2314_);
lean_dec(v___x_2313_);
lean_dec_ref(v___f_2312_);
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2310_);
lean_dec_ref(v___x_2309_);
lean_dec_ref(v_a_2307_);
lean_dec(v_rhs_2304_);
v_a_2486_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2410_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2410_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
v___jp_2323_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; lean_object* v___x_2337_; 
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2307_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_box(v___x_2308_);
lean_inc(v_term_2324_);
v___f_2336_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2336_, 0, v_term_2324_);
lean_closure_set(v___f_2336_, 1, v___x_2333_);
lean_closure_set(v___f_2336_, 2, v___x_2335_);
lean_closure_set(v___f_2336_, 3, v___x_2334_);
v___x_2337_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2331_, v_term_2324_, v___f_2336_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2332_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2494_ = _args[0];
lean_object* v___x_2495_ = _args[1];
lean_object* v_config_2496_ = _args[2];
lean_object* v_a_2497_ = _args[3];
lean_object* v___x_2498_ = _args[4];
lean_object* v___x_2499_ = _args[5];
lean_object* v___x_2500_ = _args[6];
lean_object* v___x_2501_ = _args[7];
lean_object* v___f_2502_ = _args[8];
lean_object* v___x_2503_ = _args[9];
lean_object* v_body_2504_ = _args[10];
lean_object* v___y_2505_ = _args[11];
lean_object* v___y_2506_ = _args[12];
lean_object* v___y_2507_ = _args[13];
lean_object* v___y_2508_ = _args[14];
lean_object* v___y_2509_ = _args[15];
lean_object* v___y_2510_ = _args[16];
lean_object* v___y_2511_ = _args[17];
lean_object* v___y_2512_ = _args[18];
_start:
{
uint8_t v___x_100201__boxed_2513_; uint8_t v___x_100203__boxed_2514_; lean_object* v_res_2515_; 
v___x_100201__boxed_2513_ = lean_unbox(v___x_2495_);
v___x_100203__boxed_2514_ = lean_unbox(v___x_2498_);
v_res_2515_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2494_, v___x_100201__boxed_2513_, v_config_2496_, v_a_2497_, v___x_100203__boxed_2514_, v___x_2499_, v___x_2500_, v___x_2501_, v___f_2502_, v___x_2503_, v_body_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2516_, lean_object* v___y_2517_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_a_2518_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_a_2518_);
lean_ctor_set(v___x_2519_, 1, v___y_2517_);
return v___x_2519_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_a_2520_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_a_2520_);
lean_ctor_set(v___x_2521_, 1, v___y_2517_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2522_, v___y_2523_);
lean_dec_ref(v_x_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2525_, lean_object* v_stx_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2525_, v_stx_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
if (lean_obj_tag(v_a_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_a_2531_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2529_, 0);
lean_dec(v_unused_2540_);
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2531_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2569_; 
v_val_2541_ = lean_ctor_get(v_a_2530_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2543_ = v_a_2530_;
v_isShared_2544_ = v_isSharedCheck_2569_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v_a_2530_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2569_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_snd_2545_; 
v_snd_2545_ = lean_ctor_get(v_val_2541_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_val_2541_);
if (lean_obj_tag(v_snd_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
lean_del_object(v___x_2543_);
v_a_2546_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2546_);
lean_dec_ref(v___x_2529_);
v_a_2547_ = lean_ctor_get(v_snd_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_snd_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2549_ = v_snd_2545_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v_snd_2545_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2552_, v_a_2546_);
lean_dec_ref(v___x_2552_);
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2568_; 
v_a_2556_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2529_);
v_a_2557_ = lean_ctor_get(v_snd_2545_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_snd_2545_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2559_ = v_snd_2545_;
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v_snd_2545_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v_a_2557_);
v___x_2562_ = v___x_2543_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2562_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2564_, v_a_2556_);
lean_dec_ref(v___x_2564_);
return v___x_2565_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2570_ = lean_ctor_get(v___x_2529_, 0);
v_a_2571_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2529_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_inc(v_a_2570_);
lean_dec(v___x_2529_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2579_, lean_object* v_stx_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2579_, v_stx_2580_, v___y_2581_, v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_currNamespace_2584_);
lean_ctor_set(v___x_2587_, 1, v___y_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2588_, v___y_2589_, v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2592_, lean_object* v_currNamespace_2593_, lean_object* v_openDecls_2594_, lean_object* v_n_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = l_Lean_ResolveName_resolveNamespace(v_env_2592_, v_currNamespace_2593_, v_openDecls_2594_, v_n_2595_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___y_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2600_, lean_object* v_currNamespace_2601_, lean_object* v_openDecls_2602_, lean_object* v_n_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2600_, v_currNamespace_2601_, v_openDecls_2602_, v_n_2603_, v___y_2604_, v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2607_, lean_object* v_declName_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
uint8_t v___x_2611_; lean_object* v_env_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2611_ = 0;
v_env_2612_ = l_Lean_Environment_setExporting(v_env_2607_, v___x_2611_);
lean_inc(v_declName_2608_);
v___x_2613_ = l_Lean_mkPrivateName(v_env_2612_, v_declName_2608_);
v___x_2614_ = 1;
lean_inc_ref(v_env_2612_);
v___x_2615_ = l_Lean_Environment_contains(v_env_2612_, v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2616_ = l_Lean_privateToUserName(v_declName_2608_);
v___x_2617_ = l_Lean_Environment_contains(v_env_2612_, v___x_2616_, v___x_2614_);
v___x_2618_ = lean_box(v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___y_2610_);
return v___x_2619_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v_env_2612_);
lean_dec(v_declName_2608_);
v___x_2620_ = lean_box(v___x_2615_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___y_2610_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2622_, lean_object* v_declName_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2622_, v_declName_2623_, v___y_2624_, v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2626_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2627_; double v___x_2628_; 
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_float_of_nat(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2631_, lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_ref_2638_; lean_object* v___x_2639_; lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2684_; 
v_ref_2638_ = lean_ctor_get(v___y_2635_, 5);
v___x_2639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v_traceState_2645_; lean_object* v_env_2646_; lean_object* v_nextMacroScope_2647_; lean_object* v_ngen_2648_; lean_object* v_auxDeclNGen_2649_; lean_object* v_cache_2650_; lean_object* v_messages_2651_; lean_object* v_infoState_2652_; lean_object* v_snapshotTasks_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2683_; 
v___x_2644_ = lean_st_ref_take(v___y_2636_);
v_traceState_2645_ = lean_ctor_get(v___x_2644_, 4);
v_env_2646_ = lean_ctor_get(v___x_2644_, 0);
v_nextMacroScope_2647_ = lean_ctor_get(v___x_2644_, 1);
v_ngen_2648_ = lean_ctor_get(v___x_2644_, 2);
v_auxDeclNGen_2649_ = lean_ctor_get(v___x_2644_, 3);
v_cache_2650_ = lean_ctor_get(v___x_2644_, 5);
v_messages_2651_ = lean_ctor_get(v___x_2644_, 6);
v_infoState_2652_ = lean_ctor_get(v___x_2644_, 7);
v_snapshotTasks_2653_ = lean_ctor_get(v___x_2644_, 8);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snapshotTasks_2653_);
lean_inc(v_infoState_2652_);
lean_inc(v_messages_2651_);
lean_inc(v_cache_2650_);
lean_inc(v_traceState_2645_);
lean_inc(v_auxDeclNGen_2649_);
lean_inc(v_ngen_2648_);
lean_inc(v_nextMacroScope_2647_);
lean_inc(v_env_2646_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2683_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
uint64_t v_tid_2657_; lean_object* v_traces_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2682_; 
v_tid_2657_ = lean_ctor_get_uint64(v_traceState_2645_, sizeof(void*)*1);
v_traces_2658_ = lean_ctor_get(v_traceState_2645_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_traceState_2645_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2660_ = v_traceState_2645_;
v_isShared_2661_ = v_isSharedCheck_2682_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_traces_2658_);
lean_dec(v_traceState_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2682_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; double v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2662_ = lean_box(0);
v___x_2663_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2664_ = 0;
v___x_2665_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2666_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2666_, 0, v_cls_2631_);
lean_ctor_set(v___x_2666_, 1, v___x_2662_);
lean_ctor_set(v___x_2666_, 2, v___x_2665_);
lean_ctor_set_float(v___x_2666_, sizeof(void*)*3, v___x_2663_);
lean_ctor_set_float(v___x_2666_, sizeof(void*)*3 + 8, v___x_2663_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*3 + 16, v___x_2664_);
v___x_2667_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2668_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v_a_2640_);
lean_ctor_set(v___x_2668_, 2, v___x_2667_);
lean_inc(v_ref_2638_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_ref_2638_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_PersistentArray_push___redArg(v_traces_2658_, v___x_2669_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2670_);
v___x_2672_ = v___x_2660_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2670_);
lean_ctor_set_uint64(v_reuseFailAlloc_2681_, sizeof(void*)*1, v_tid_2657_);
v___x_2672_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 4, v___x_2672_);
v___x_2674_ = v___x_2655_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_env_2646_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_nextMacroScope_2647_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_ngen_2648_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_auxDeclNGen_2649_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2680_, 5, v_cache_2650_);
lean_ctor_set(v_reuseFailAlloc_2680_, 6, v_messages_2651_);
lean_ctor_set(v_reuseFailAlloc_2680_, 7, v_infoState_2652_);
lean_ctor_set(v_reuseFailAlloc_2680_, 8, v_snapshotTasks_2653_);
v___x_2674_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2675_ = lean_st_ref_set(v___y_2636_, v___x_2674_);
v___x_2676_ = lean_box(0);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2676_);
v___x_2678_ = v___x_2642_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2685_, lean_object* v_msg_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2685_, v_msg_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
if (lean_obj_tag(v_as_2696_) == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_box(0);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
else
{
lean_object* v_options_2707_; uint8_t v_hasTrace_2708_; 
v_options_2707_ = lean_ctor_get(v___y_2702_, 2);
v_hasTrace_2708_ = lean_ctor_get_uint8(v_options_2707_, sizeof(void*)*1);
if (v_hasTrace_2708_ == 0)
{
lean_object* v_tail_2709_; 
v_tail_2709_ = lean_ctor_get(v_as_2696_, 1);
lean_inc(v_tail_2709_);
lean_dec_ref(v_as_2696_);
v_as_2696_ = v_tail_2709_;
goto _start;
}
else
{
lean_object* v_head_2711_; lean_object* v_tail_2712_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; lean_object* v_inheritedTraceOptions_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_head_2711_ = lean_ctor_get(v_as_2696_, 0);
lean_inc(v_head_2711_);
v_tail_2712_ = lean_ctor_get(v_as_2696_, 1);
lean_inc(v_tail_2712_);
lean_dec_ref(v_as_2696_);
v_fst_2713_ = lean_ctor_get(v_head_2711_, 0);
lean_inc_n(v_fst_2713_, 2);
v_snd_2714_ = lean_ctor_get(v_head_2711_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_head_2711_);
v_inheritedTraceOptions_2715_ = lean_ctor_get(v___y_2702_, 13);
v___x_2716_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2717_ = l_Lean_Name_append(v___x_2716_, v_fst_2713_);
v___x_2718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2715_, v_options_2707_, v___x_2717_);
lean_dec(v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec(v_snd_2714_);
lean_dec(v_fst_2713_);
v_as_2696_ = v_tail_2712_;
goto _start;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_snd_2714_);
v___x_2721_ = l_Lean_MessageData_ofFormat(v___x_2720_);
v___x_2722_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2713_, v___x_2721_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_dec_ref(v___x_2722_);
v_as_2696_ = v_tail_2712_;
goto _start;
}
else
{
lean_dec(v_tail_2712_);
return v___x_2722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(lean_object* v_keys_2734_, lean_object* v_i_2735_, lean_object* v_k_2736_){
_start:
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = lean_array_get_size(v_keys_2734_);
v___x_2738_ = lean_nat_dec_lt(v_i_2735_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_dec(v_i_2735_);
return v___x_2738_;
}
else
{
lean_object* v_k_x27_2739_; uint8_t v___x_2740_; 
v_k_x27_2739_ = lean_array_fget_borrowed(v_keys_2734_, v_i_2735_);
v___x_2740_ = l_Lean_instBEqExtraModUse_beq(v_k_2736_, v_k_x27_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_nat_add(v_i_2735_, v___x_2741_);
lean_dec(v_i_2735_);
v_i_2735_ = v___x_2742_;
goto _start;
}
else
{
lean_dec(v_i_2735_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg___boxed(lean_object* v_keys_2744_, lean_object* v_i_2745_, lean_object* v_k_2746_){
_start:
{
uint8_t v_res_2747_; lean_object* v_r_2748_; 
v_res_2747_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_keys_2744_, v_i_2745_, v_k_2746_);
lean_dec_ref(v_k_2746_);
lean_dec_ref(v_keys_2744_);
v_r_2748_ = lean_box(v_res_2747_);
return v_r_2748_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2749_, size_t v_x_2750_, lean_object* v_x_2751_){
_start:
{
if (lean_obj_tag(v_x_2749_) == 0)
{
lean_object* v_es_2752_; lean_object* v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; lean_object* v_j_2757_; lean_object* v___x_2758_; 
v_es_2752_ = lean_ctor_get(v_x_2749_, 0);
v___x_2753_ = lean_box(2);
v___x_2754_ = ((size_t)5ULL);
v___x_2755_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2756_ = lean_usize_land(v_x_2750_, v___x_2755_);
v_j_2757_ = lean_usize_to_nat(v___x_2756_);
v___x_2758_ = lean_array_get_borrowed(v___x_2753_, v_es_2752_, v_j_2757_);
lean_dec(v_j_2757_);
switch(lean_obj_tag(v___x_2758_))
{
case 0:
{
lean_object* v_key_2759_; uint8_t v___x_2760_; 
v_key_2759_ = lean_ctor_get(v___x_2758_, 0);
v___x_2760_ = l_Lean_instBEqExtraModUse_beq(v_x_2751_, v_key_2759_);
return v___x_2760_;
}
case 1:
{
lean_object* v_node_2761_; size_t v___x_2762_; 
v_node_2761_ = lean_ctor_get(v___x_2758_, 0);
v___x_2762_ = lean_usize_shift_right(v_x_2750_, v___x_2754_);
v_x_2749_ = v_node_2761_;
v_x_2750_ = v___x_2762_;
goto _start;
}
default: 
{
uint8_t v___x_2764_; 
v___x_2764_ = 0;
return v___x_2764_;
}
}
}
else
{
lean_object* v_ks_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_ks_2765_ = lean_ctor_get(v_x_2749_, 0);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_ks_2765_, v___x_2766_, v_x_2751_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_){
_start:
{
size_t v_x_100951__boxed_2771_; uint8_t v_res_2772_; lean_object* v_r_2773_; 
v_x_100951__boxed_2771_ = lean_unbox_usize(v_x_2769_);
lean_dec(v_x_2769_);
v_res_2772_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2768_, v_x_100951__boxed_2771_, v_x_2770_);
lean_dec_ref(v_x_2770_);
lean_dec_ref(v_x_2768_);
v_r_2773_ = lean_box(v_res_2772_);
return v_r_2773_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
uint64_t v___x_2776_; size_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = l_Lean_instHashableExtraModUse_hash(v_x_2775_);
v___x_2777_ = lean_uint64_to_usize(v___x_2776_);
v___x_2778_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2774_, v___x_2777_, v_x_2775_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
uint8_t v_res_2781_; lean_object* v_r_2782_; 
v_res_2781_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2779_, v_x_2780_);
lean_dec_ref(v_x_2780_);
lean_dec_ref(v_x_2779_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2787_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2786_, v___x_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2788_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2794_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_ctor_set(v___x_2794_, 2, v___x_2793_);
lean_ctor_set(v___x_2794_, 3, v___x_2793_);
lean_ctor_set(v___x_2794_, 4, v___x_2793_);
lean_ctor_set(v___x_2794_, 5, v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2800_ = l_Lean_stringToMessageData(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2803_ = l_Lean_stringToMessageData(v___x_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2805_ = l_Lean_stringToMessageData(v___x_2804_);
return v___x_2805_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_cls_2806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2807_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2808_ = l_Lean_Name_append(v___x_2807_, v_cls_2806_);
return v___x_2808_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2811_ = l_Lean_stringToMessageData(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2819_, uint8_t v_isMeta_2820_, lean_object* v_hint_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v_env_2831_; uint8_t v_isExporting_2832_; lean_object* v___x_2833_; lean_object* v_env_2834_; lean_object* v___x_2835_; lean_object* v_entry_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2830_ = lean_st_ref_get(v___y_2828_);
v_env_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc_ref(v_env_2831_);
lean_dec(v___x_2830_);
v_isExporting_2832_ = lean_ctor_get_uint8(v_env_2831_, sizeof(void*)*8);
lean_dec_ref(v_env_2831_);
v___x_2833_ = lean_st_ref_get(v___y_2828_);
v_env_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc_ref(v_env_2834_);
lean_dec(v___x_2833_);
v___x_2835_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2819_);
v_entry_2836_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2836_, 0, v_mod_2819_);
lean_ctor_set_uint8(v_entry_2836_, sizeof(void*)*1, v_isExporting_2832_);
lean_ctor_set_uint8(v_entry_2836_, sizeof(void*)*1 + 1, v_isMeta_2820_);
v___x_2837_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2838_ = lean_box(1);
v___x_2839_ = lean_box(0);
v___x_2882_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2835_, v___x_2837_, v_env_2834_, v___x_2838_, v___x_2839_);
v___x_2883_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2882_, v_entry_2836_);
lean_dec(v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v_options_2884_; uint8_t v_hasTrace_2885_; 
v_options_2884_ = lean_ctor_get(v___y_2827_, 2);
v_hasTrace_2885_ = lean_ctor_get_uint8(v_options_2884_, sizeof(void*)*1);
if (v_hasTrace_2885_ == 0)
{
lean_dec(v_hint_2821_);
lean_dec(v_mod_2819_);
v___y_2841_ = v___y_2826_;
v___y_2842_ = v___y_2828_;
goto v___jp_2840_;
}
else
{
lean_object* v_inheritedTraceOptions_2886_; lean_object* v_cls_2887_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_inheritedTraceOptions_2886_ = lean_ctor_get(v___y_2827_, 13);
v_cls_2887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2907_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2886_, v_options_2884_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_dec(v_hint_2821_);
lean_dec(v_mod_2819_);
v___y_2841_ = v___y_2826_;
v___y_2842_ = v___y_2828_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2909_; lean_object* v___y_2911_; 
v___x_2909_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2832_ == 0)
{
lean_object* v___x_2918_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2911_ = v___x_2918_;
goto v___jp_2910_;
}
else
{
lean_object* v___x_2919_; 
v___x_2919_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2911_ = v___x_2919_;
goto v___jp_2910_;
}
v___jp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_inc_ref(v___y_2911_);
v___x_2912_ = l_Lean_stringToMessageData(v___y_2911_);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2909_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
if (v_isMeta_2820_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2894_ = v___x_2915_;
v___y_2895_ = v___x_2916_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2894_ = v___x_2915_;
v___y_2895_ = v___x_2917_;
goto v___jp_2893_;
}
}
}
v___jp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___y_2889_);
lean_ctor_set(v___x_2891_, 1, v___y_2890_);
v___x_2892_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2887_, v___x_2891_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref(v___x_2892_);
v___y_2841_ = v___y_2826_;
v___y_2842_ = v___y_2828_;
goto v___jp_2840_;
}
else
{
lean_dec_ref(v_entry_2836_);
return v___x_2892_;
}
}
v___jp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
lean_inc_ref(v___y_2895_);
v___x_2896_ = l_Lean_stringToMessageData(v___y_2895_);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___y_2894_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = l_Lean_MessageData_ofName(v_mod_2819_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_Name_isAnonymous(v_hint_2821_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2904_ = l_Lean_MessageData_ofName(v_hint_2821_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___y_2889_ = v___x_2901_;
v___y_2890_ = v___x_2905_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2906_; 
lean_dec(v_hint_2821_);
v___x_2906_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2889_ = v___x_2901_;
v___y_2890_ = v___x_2906_;
goto v___jp_2888_;
}
}
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec_ref(v_entry_2836_);
lean_dec(v_hint_2821_);
lean_dec(v_mod_2819_);
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
v___jp_2840_:
{
lean_object* v___x_2843_; lean_object* v_toEnvExtension_2844_; lean_object* v_env_2845_; lean_object* v_nextMacroScope_2846_; lean_object* v_ngen_2847_; lean_object* v_auxDeclNGen_2848_; lean_object* v_traceState_2849_; lean_object* v_messages_2850_; lean_object* v_infoState_2851_; lean_object* v_snapshotTasks_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2880_; 
v___x_2843_ = lean_st_ref_take(v___y_2842_);
v_toEnvExtension_2844_ = lean_ctor_get(v___x_2837_, 0);
v_env_2845_ = lean_ctor_get(v___x_2843_, 0);
v_nextMacroScope_2846_ = lean_ctor_get(v___x_2843_, 1);
v_ngen_2847_ = lean_ctor_get(v___x_2843_, 2);
v_auxDeclNGen_2848_ = lean_ctor_get(v___x_2843_, 3);
v_traceState_2849_ = lean_ctor_get(v___x_2843_, 4);
v_messages_2850_ = lean_ctor_get(v___x_2843_, 6);
v_infoState_2851_ = lean_ctor_get(v___x_2843_, 7);
v_snapshotTasks_2852_ = lean_ctor_get(v___x_2843_, 8);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v___x_2843_, 5);
lean_dec(v_unused_2881_);
v___x_2854_ = v___x_2843_;
v_isShared_2855_ = v_isSharedCheck_2880_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_snapshotTasks_2852_);
lean_inc(v_infoState_2851_);
lean_inc(v_messages_2850_);
lean_inc(v_traceState_2849_);
lean_inc(v_auxDeclNGen_2848_);
lean_inc(v_ngen_2847_);
lean_inc(v_nextMacroScope_2846_);
lean_inc(v_env_2845_);
lean_dec(v___x_2843_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2880_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v_asyncMode_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v_asyncMode_2856_ = lean_ctor_get(v_toEnvExtension_2844_, 2);
v___x_2857_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2837_, v_env_2845_, v_entry_2836_, v_asyncMode_2856_, v___x_2839_);
v___x_2858_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 5, v___x_2858_);
lean_ctor_set(v___x_2854_, 0, v___x_2857_);
v___x_2860_ = v___x_2854_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_nextMacroScope_2846_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_ngen_2847_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_auxDeclNGen_2848_);
lean_ctor_set(v_reuseFailAlloc_2879_, 4, v_traceState_2849_);
lean_ctor_set(v_reuseFailAlloc_2879_, 5, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2879_, 6, v_messages_2850_);
lean_ctor_set(v_reuseFailAlloc_2879_, 7, v_infoState_2851_);
lean_ctor_set(v_reuseFailAlloc_2879_, 8, v_snapshotTasks_2852_);
v___x_2860_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v_mctx_2863_; lean_object* v_zetaDeltaFVarIds_2864_; lean_object* v_postponed_2865_; lean_object* v_diag_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2877_; 
v___x_2861_ = lean_st_ref_set(v___y_2842_, v___x_2860_);
v___x_2862_ = lean_st_ref_take(v___y_2841_);
v_mctx_2863_ = lean_ctor_get(v___x_2862_, 0);
v_zetaDeltaFVarIds_2864_ = lean_ctor_get(v___x_2862_, 2);
v_postponed_2865_ = lean_ctor_get(v___x_2862_, 3);
v_diag_2866_ = lean_ctor_get(v___x_2862_, 4);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v___x_2862_, 1);
lean_dec(v_unused_2878_);
v___x_2868_ = v___x_2862_;
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_diag_2866_);
lean_inc(v_postponed_2865_);
lean_inc(v_zetaDeltaFVarIds_2864_);
lean_inc(v_mctx_2863_);
lean_dec(v___x_2862_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2877_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_mctx_2863_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_zetaDeltaFVarIds_2864_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_postponed_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_diag_2866_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = lean_st_ref_set(v___y_2841_, v___x_2872_);
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2922_, lean_object* v_isMeta_2923_, lean_object* v_hint_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
uint8_t v_isMeta_boxed_2933_; lean_object* v_res_2934_; 
v_isMeta_boxed_2933_ = lean_unbox(v_isMeta_2923_);
v_res_2934_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2922_, v_isMeta_boxed_2933_, v_hint_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2935_, lean_object* v_declName_2936_, lean_object* v_as_2937_, size_t v_sz_2938_, size_t v_i_2939_, lean_object* v_b_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_usize_dec_lt(v_i_2939_, v_sz_2938_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
lean_dec(v_declName_2936_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_b_2940_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v_modules_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v_toImport_2956_; lean_object* v_module_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; 
v___x_2951_ = l_Lean_Environment_header(v___x_2935_);
v_modules_2952_ = lean_ctor_get(v___x_2951_, 3);
lean_inc_ref(v_modules_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2954_ = lean_array_uget_borrowed(v_as_2937_, v_i_2939_);
v___x_2955_ = lean_array_get(v___x_2953_, v_modules_2952_, v_a_2954_);
lean_dec_ref(v_modules_2952_);
v_toImport_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc_ref(v_toImport_2956_);
lean_dec(v___x_2955_);
v_module_2957_ = lean_ctor_get(v_toImport_2956_, 0);
lean_inc(v_module_2957_);
lean_dec_ref(v_toImport_2956_);
v___x_2958_ = 0;
lean_inc(v_declName_2936_);
v___x_2959_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2957_, v___x_2958_, v_declName_2936_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; 
lean_dec_ref(v___x_2959_);
v___x_2960_ = lean_box(0);
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = lean_usize_add(v_i_2939_, v___x_2961_);
v_i_2939_ = v___x_2962_;
v_b_2940_ = v___x_2960_;
goto _start;
}
else
{
lean_dec(v_declName_2936_);
return v___x_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2964_, lean_object* v_declName_2965_, lean_object* v_as_2966_, lean_object* v_sz_2967_, lean_object* v_i_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
size_t v_sz_boxed_2978_; size_t v_i_boxed_2979_; lean_object* v_res_2980_; 
v_sz_boxed_2978_ = lean_unbox_usize(v_sz_2967_);
lean_dec(v_sz_2967_);
v_i_boxed_2979_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2964_, v_declName_2965_, v_as_2966_, v_sz_boxed_2978_, v_i_boxed_2979_, v_b_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v_as_2966_);
lean_dec_ref(v___x_2964_);
return v_res_2980_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2984_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2985_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2984_, v___x_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2988_, uint8_t v_isMeta_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v_env_3002_; lean_object* v___y_3004_; lean_object* v___x_3017_; 
v___x_2998_ = lean_st_ref_get(v___y_2996_);
v_env_3002_ = lean_ctor_get(v___x_2998_, 0);
lean_inc_ref(v_env_3002_);
lean_dec(v___x_2998_);
v___x_3017_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3002_, v_declName_2988_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2988_);
goto v___jp_2999_;
}
else
{
lean_object* v_val_3018_; lean_object* v___x_3019_; lean_object* v_modules_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_val_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3018_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Lean_Environment_header(v_env_3002_);
v_modules_3020_ = lean_ctor_get(v___x_3019_, 3);
lean_inc_ref(v_modules_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_array_get_size(v_modules_3020_);
v___x_3022_ = lean_nat_dec_lt(v_val_3018_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_dec_ref(v_modules_3020_);
lean_dec(v_val_3018_);
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2988_);
goto v___jp_2999_;
}
else
{
lean_object* v___x_3023_; lean_object* v_env_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___y_3028_; 
v___x_3023_ = lean_st_ref_get(v___y_2996_);
v_env_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_ref(v_env_3024_);
lean_dec(v___x_3023_);
v___x_3025_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_3026_ = lean_array_fget(v_modules_3020_, v_val_3018_);
lean_dec(v_val_3018_);
lean_dec_ref(v_modules_3020_);
if (v_isMeta_2989_ == 0)
{
lean_dec_ref(v_env_3024_);
v___y_3028_ = v_isMeta_2989_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3039_; 
lean_inc(v_declName_2988_);
v___x_3039_ = l_Lean_isMarkedMeta(v_env_3024_, v_declName_2988_);
if (v___x_3039_ == 0)
{
v___y_3028_ = v_isMeta_2989_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3040_; 
v___x_3040_ = 0;
v___y_3028_ = v___x_3040_;
goto v___jp_3027_;
}
}
v___jp_3027_:
{
lean_object* v_toImport_3029_; lean_object* v_module_3030_; lean_object* v___x_3031_; 
v_toImport_3029_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_toImport_3029_);
lean_dec(v___x_3026_);
v_module_3030_ = lean_ctor_get(v_toImport_3029_, 0);
lean_inc(v_module_3030_);
lean_dec_ref(v_toImport_3029_);
lean_inc(v_declName_2988_);
v___x_3031_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_3030_, v___y_3028_, v_declName_2988_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref(v___x_3031_);
v___x_3032_ = l_Lean_indirectModUseExt;
v___x_3033_ = lean_box(1);
v___x_3034_ = lean_box(0);
lean_inc_ref(v_env_3002_);
v___x_3035_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3025_, v___x_3032_, v_env_3002_, v___x_3033_, v___x_3034_);
v___x_3036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_3035_, v_declName_2988_);
lean_dec(v___x_3035_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_3004_ = v___x_3037_;
goto v___jp_3003_;
}
else
{
lean_object* v_val_3038_; 
v_val_3038_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_val_3038_);
lean_dec_ref(v___x_3036_);
v___y_3004_ = v_val_3038_;
goto v___jp_3003_;
}
}
else
{
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2988_);
return v___x_3031_;
}
}
}
}
v___jp_2999_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; size_t v_sz_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = lean_box(0);
v_sz_3006_ = lean_array_size(v___y_3004_);
v___x_3007_ = ((size_t)0ULL);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_3002_, v_declName_2988_, v___y_3004_, v_sz_3006_, v___x_3007_, v___x_3005_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v_env_3002_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_3008_, 0);
lean_dec(v_unused_3016_);
v___x_3010_ = v___x_3008_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v___x_3008_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3005_);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3005_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_3041_, lean_object* v_isMeta_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v_isMeta_boxed_3051_; lean_object* v_res_3052_; 
v_isMeta_boxed_3051_ = lean_unbox(v_isMeta_3042_);
v_res_3052_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_3041_, v_isMeta_boxed_3051_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_3053_, lean_object* v_b_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
if (lean_obj_tag(v_as_x27_3053_) == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_b_3054_);
return v___x_3063_;
}
else
{
lean_object* v_head_3064_; lean_object* v_tail_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; 
v_head_3064_ = lean_ctor_get(v_as_x27_3053_, 0);
v_tail_3065_ = lean_ctor_get(v_as_x27_3053_, 1);
v___x_3066_ = 1;
lean_inc(v_head_3064_);
v___x_3067_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_3064_, v___x_3066_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref(v___x_3067_);
v___x_3068_ = lean_box(0);
v_as_x27_3053_ = v_tail_3065_;
v_b_3054_ = v___x_3068_;
goto _start;
}
else
{
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3070_, v_b_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v_as_x27_3070_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_3081_, lean_object* v_options_3082_, lean_object* v_currNamespace_3083_, lean_object* v_openDecls_3084_, lean_object* v_n_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = l_Lean_ResolveName_resolveGlobalName(v_env_3081_, v_options_3082_, v_currNamespace_3083_, v_openDecls_3084_, v_n_3085_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___y_3087_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_3090_, lean_object* v_options_3091_, lean_object* v_currNamespace_3092_, lean_object* v_openDecls_3093_, lean_object* v_n_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_3090_, v_options_3091_, v_currNamespace_3092_, v_openDecls_3093_, v_n_3094_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec_ref(v_options_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_fileName_3105_; lean_object* v_fileMap_3106_; lean_object* v_options_3107_; lean_object* v_currRecDepth_3108_; lean_object* v_maxRecDepth_3109_; lean_object* v_ref_3110_; lean_object* v_currNamespace_3111_; lean_object* v_openDecls_3112_; lean_object* v_initHeartbeats_3113_; lean_object* v_maxHeartbeats_3114_; lean_object* v_quotContext_3115_; lean_object* v_currMacroScope_3116_; uint8_t v_diag_3117_; lean_object* v_cancelTk_x3f_3118_; uint8_t v_suppressElabErrors_3119_; lean_object* v_inheritedTraceOptions_3120_; lean_object* v_ref_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_fileName_3105_ = lean_ctor_get(v___y_3102_, 0);
v_fileMap_3106_ = lean_ctor_get(v___y_3102_, 1);
v_options_3107_ = lean_ctor_get(v___y_3102_, 2);
v_currRecDepth_3108_ = lean_ctor_get(v___y_3102_, 3);
v_maxRecDepth_3109_ = lean_ctor_get(v___y_3102_, 4);
v_ref_3110_ = lean_ctor_get(v___y_3102_, 5);
v_currNamespace_3111_ = lean_ctor_get(v___y_3102_, 6);
v_openDecls_3112_ = lean_ctor_get(v___y_3102_, 7);
v_initHeartbeats_3113_ = lean_ctor_get(v___y_3102_, 8);
v_maxHeartbeats_3114_ = lean_ctor_get(v___y_3102_, 9);
v_quotContext_3115_ = lean_ctor_get(v___y_3102_, 10);
v_currMacroScope_3116_ = lean_ctor_get(v___y_3102_, 11);
v_diag_3117_ = lean_ctor_get_uint8(v___y_3102_, sizeof(void*)*14);
v_cancelTk_x3f_3118_ = lean_ctor_get(v___y_3102_, 12);
v_suppressElabErrors_3119_ = lean_ctor_get_uint8(v___y_3102_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3120_ = lean_ctor_get(v___y_3102_, 13);
v_ref_3121_ = l_Lean_replaceRef(v_ref_3098_, v_ref_3110_);
lean_inc_ref(v_inheritedTraceOptions_3120_);
lean_inc(v_cancelTk_x3f_3118_);
lean_inc(v_currMacroScope_3116_);
lean_inc(v_quotContext_3115_);
lean_inc(v_maxHeartbeats_3114_);
lean_inc(v_initHeartbeats_3113_);
lean_inc(v_openDecls_3112_);
lean_inc(v_currNamespace_3111_);
lean_inc(v_maxRecDepth_3109_);
lean_inc(v_currRecDepth_3108_);
lean_inc_ref(v_options_3107_);
lean_inc_ref(v_fileMap_3106_);
lean_inc_ref(v_fileName_3105_);
v___x_3122_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3122_, 0, v_fileName_3105_);
lean_ctor_set(v___x_3122_, 1, v_fileMap_3106_);
lean_ctor_set(v___x_3122_, 2, v_options_3107_);
lean_ctor_set(v___x_3122_, 3, v_currRecDepth_3108_);
lean_ctor_set(v___x_3122_, 4, v_maxRecDepth_3109_);
lean_ctor_set(v___x_3122_, 5, v_ref_3121_);
lean_ctor_set(v___x_3122_, 6, v_currNamespace_3111_);
lean_ctor_set(v___x_3122_, 7, v_openDecls_3112_);
lean_ctor_set(v___x_3122_, 8, v_initHeartbeats_3113_);
lean_ctor_set(v___x_3122_, 9, v_maxHeartbeats_3114_);
lean_ctor_set(v___x_3122_, 10, v_quotContext_3115_);
lean_ctor_set(v___x_3122_, 11, v_currMacroScope_3116_);
lean_ctor_set(v___x_3122_, 12, v_cancelTk_x3f_3118_);
lean_ctor_set(v___x_3122_, 13, v_inheritedTraceOptions_3120_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*14, v_diag_3117_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*14 + 1, v_suppressElabErrors_3119_);
v___x_3123_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_3099_, v___y_3100_, v___y_3101_, v___x_3122_, v___y_3103_);
lean_dec_ref(v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_3124_, lean_object* v_msg_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3124_, v_msg_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v_ref_3124_);
return v_res_3131_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = l_Lean_maxRecDepthErrorMessage;
v___x_3138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_3140_ = l_Lean_MessageData_ofFormat(v___x_3139_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3142_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3143_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v___x_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_ref_3144_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; lean_object* v_env_3163_; lean_object* v_options_3164_; lean_object* v_currRecDepth_3165_; lean_object* v_maxRecDepth_3166_; lean_object* v_ref_3167_; lean_object* v_currNamespace_3168_; lean_object* v_openDecls_3169_; lean_object* v_quotContext_3170_; lean_object* v_currMacroScope_3171_; lean_object* v___x_3172_; lean_object* v_nextMacroScope_3173_; lean_object* v___f_3174_; lean_object* v___f_3175_; lean_object* v___f_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; lean_object* v_methods_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3162_ = lean_st_ref_get(v___y_3160_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref_n(v_env_3163_, 4);
lean_dec(v___x_3162_);
v_options_3164_ = lean_ctor_get(v___y_3159_, 2);
v_currRecDepth_3165_ = lean_ctor_get(v___y_3159_, 3);
v_maxRecDepth_3166_ = lean_ctor_get(v___y_3159_, 4);
v_ref_3167_ = lean_ctor_get(v___y_3159_, 5);
v_currNamespace_3168_ = lean_ctor_get(v___y_3159_, 6);
v_openDecls_3169_ = lean_ctor_get(v___y_3159_, 7);
v_quotContext_3170_ = lean_ctor_get(v___y_3159_, 10);
v_currMacroScope_3171_ = lean_ctor_get(v___y_3159_, 11);
v___x_3172_ = lean_st_ref_get(v___y_3160_);
v_nextMacroScope_3173_ = lean_ctor_get(v___x_3172_, 1);
lean_inc(v_nextMacroScope_3173_);
lean_dec(v___x_3172_);
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3174_, 0, v_env_3163_);
v___f_3175_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3175_, 0, v_env_3163_);
lean_inc_n(v_openDecls_3169_, 2);
lean_inc_n(v_currNamespace_3168_, 3);
v___f_3176_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3176_, 0, v_env_3163_);
lean_closure_set(v___f_3176_, 1, v_currNamespace_3168_);
lean_closure_set(v___f_3176_, 2, v_openDecls_3169_);
v___f_3177_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3177_, 0, v_currNamespace_3168_);
lean_inc_ref(v_options_3164_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3178_, 0, v_env_3163_);
lean_closure_set(v___f_3178_, 1, v_options_3164_);
lean_closure_set(v___f_3178_, 2, v_currNamespace_3168_);
lean_closure_set(v___f_3178_, 3, v_openDecls_3169_);
v_methods_3179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3179_, 0, v___f_3174_);
lean_ctor_set(v_methods_3179_, 1, v___f_3177_);
lean_ctor_set(v_methods_3179_, 2, v___f_3175_);
lean_ctor_set(v_methods_3179_, 3, v___f_3176_);
lean_ctor_set(v_methods_3179_, 4, v___f_3178_);
lean_inc(v_ref_3167_);
lean_inc(v_maxRecDepth_3166_);
lean_inc(v_currRecDepth_3165_);
lean_inc(v_currMacroScope_3171_);
lean_inc(v_quotContext_3170_);
v___x_3180_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3180_, 0, v_methods_3179_);
lean_ctor_set(v___x_3180_, 1, v_quotContext_3170_);
lean_ctor_set(v___x_3180_, 2, v_currMacroScope_3171_);
lean_ctor_set(v___x_3180_, 3, v_currRecDepth_3165_);
lean_ctor_set(v___x_3180_, 4, v_maxRecDepth_3166_);
lean_ctor_set(v___x_3180_, 5, v_ref_3167_);
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3182_, 0, v_nextMacroScope_3173_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
lean_ctor_set(v___x_3182_, 2, v___x_3181_);
v___x_3183_ = lean_apply_2(v_x_3153_, v___x_3180_, v___x_3182_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v_a_3185_; lean_object* v_macroScope_3186_; lean_object* v_traceMsgs_3187_; lean_object* v_expandedMacroDecls_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 1);
lean_inc(v_a_3184_);
v_a_3185_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3183_);
v_macroScope_3186_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_macroScope_3186_);
v_traceMsgs_3187_ = lean_ctor_get(v_a_3184_, 1);
lean_inc(v_traceMsgs_3187_);
v_expandedMacroDecls_3188_ = lean_ctor_get(v_a_3184_, 2);
lean_inc(v_expandedMacroDecls_3188_);
lean_dec(v_a_3184_);
v___x_3189_ = lean_box(0);
v___x_3190_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3188_, v___x_3189_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v_expandedMacroDecls_3188_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3191_; lean_object* v_env_3192_; lean_object* v_ngen_3193_; lean_object* v_auxDeclNGen_3194_; lean_object* v_traceState_3195_; lean_object* v_cache_3196_; lean_object* v_messages_3197_; lean_object* v_infoState_3198_; lean_object* v_snapshotTasks_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v___x_3190_);
v___x_3191_ = lean_st_ref_take(v___y_3160_);
v_env_3192_ = lean_ctor_get(v___x_3191_, 0);
v_ngen_3193_ = lean_ctor_get(v___x_3191_, 2);
v_auxDeclNGen_3194_ = lean_ctor_get(v___x_3191_, 3);
v_traceState_3195_ = lean_ctor_get(v___x_3191_, 4);
v_cache_3196_ = lean_ctor_get(v___x_3191_, 5);
v_messages_3197_ = lean_ctor_get(v___x_3191_, 6);
v_infoState_3198_ = lean_ctor_get(v___x_3191_, 7);
v_snapshotTasks_3199_ = lean_ctor_get(v___x_3191_, 8);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v___x_3191_, 1);
lean_dec(v_unused_3226_);
v___x_3201_ = v___x_3191_;
v_isShared_3202_ = v_isSharedCheck_3225_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snapshotTasks_3199_);
lean_inc(v_infoState_3198_);
lean_inc(v_messages_3197_);
lean_inc(v_cache_3196_);
lean_inc(v_traceState_3195_);
lean_inc(v_auxDeclNGen_3194_);
lean_inc(v_ngen_3193_);
lean_inc(v_env_3192_);
lean_dec(v___x_3191_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3225_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_macroScope_3186_);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_env_3192_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_macroScope_3186_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_ngen_3193_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_auxDeclNGen_3194_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_traceState_3195_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_cache_3196_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_messages_3197_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_infoState_3198_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_snapshotTasks_3199_);
v___x_3204_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_st_ref_set(v___y_3160_, v___x_3204_);
v___x_3206_ = l_List_reverse___redArg(v_traceMsgs_3187_);
v___x_3207_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3206_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3207_, 0);
lean_dec(v_unused_3215_);
v___x_3209_ = v___x_3207_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v___x_3207_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v_a_3185_);
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3185_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_a_3185_);
v_a_3216_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3207_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3207_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v_traceMsgs_3187_);
lean_dec(v_macroScope_3186_);
lean_dec(v_a_3185_);
v_a_3227_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3190_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3190_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3183_);
if (lean_obj_tag(v_a_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_a_3236_ = lean_ctor_get(v_a_3235_, 0);
lean_inc(v_a_3236_);
v_a_3237_ = lean_ctor_get(v_a_3235_, 1);
lean_inc_ref(v_a_3237_);
lean_dec_ref(v_a_3235_);
v___x_3238_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3239_ = lean_string_dec_eq(v_a_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3240_, 0, v_a_3237_);
v___x_3241_ = l_Lean_MessageData_ofFormat(v___x_3240_);
v___x_3242_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3236_, v___x_3241_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v_a_3236_);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; 
lean_dec_ref(v_a_3237_);
v___x_3243_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3236_);
return v___x_3243_;
}
}
else
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_quotContext_3259_; lean_object* v_currMacroScope_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_quotContext_3259_ = lean_ctor_get(v___y_3256_, 10);
lean_inc(v_quotContext_3259_);
v_currMacroScope_3260_ = lean_ctor_get(v___y_3256_, 11);
lean_inc(v_currMacroScope_3260_);
lean_dec_ref(v___y_3256_);
v___x_3261_ = l_Lean_addMacroScope(v_quotContext_3259_, v___x_3255_, v_currMacroScope_3260_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___f_3276_; lean_object* v___x_3277_; 
v___f_3276_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3277_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3276_, v___y_3273_, v___y_3274_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3282_, uint8_t v_canonical_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3301_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3301_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3301_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = l_Lean_mkIdentFrom(v_ref_3282_, v_a_3293_, v_canonical_3283_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3297_);
v___x_3299_ = v___x_3295_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
v_a_3302_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3292_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3292_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3310_, lean_object* v_canonical_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v_canonical_boxed_3320_; lean_object* v_res_3321_; 
v_canonical_boxed_3320_ = lean_unbox(v_canonical_3311_);
v_res_3321_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3310_, v_canonical_boxed_3320_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v_ref_3310_);
return v_res_3321_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3334_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3335_ = l_Lean_Name_append(v___x_3334_, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3338_ = l_Lean_stringToMessageData(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3345_, lean_object* v_letOrReassign_3346_, lean_object* v_decl_3347_, lean_object* v_tk_3348_, lean_object* v_dec_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3345_, v_letOrReassign_3346_, v_decl_3347_, v_tk_3348_, v_dec_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3359_, lean_object* v_letOrReassign_3360_, lean_object* v_decl_3361_, lean_object* v_tk_3362_, lean_object* v_dec_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3359_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref(v___x_3372_);
lean_inc(v_decl_3361_);
v___x_3373_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3361_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3360_, v_a_3374_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v___x_3376_; 
lean_dec_ref(v___x_3375_);
v___x_3376_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3363_, v_tk_3362_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref(v___x_3376_);
v___x_3378_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3360_, v_decl_3361_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v_doBlockResultType_3380_; lean_object* v___x_3381_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v_doBlockResultType_3380_ = lean_ctor_get(v_a_3364_, 3);
lean_inc_ref(v_doBlockResultType_3380_);
v___x_3381_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_3380_, v_a_3364_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3600_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3600_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3600_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3387_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3379_);
v___x_3390_ = l_Lean_Syntax_isOfKind(v_a_3379_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
lean_dec(v_a_3379_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_tk_3362_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v___x_3391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3391_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = l_Lean_Syntax_getArg(v_a_3379_, v___x_3392_);
lean_dec(v_a_3379_);
v___x_3394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3393_);
v___x_3395_ = l_Lean_Syntax_isOfKind(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; uint8_t v___x_3397_; 
lean_dec(v_tk_3362_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3393_);
v___x_3397_ = l_Lean_Syntax_isOfKind(v___x_3393_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3393_);
v___x_3399_ = l_Lean_Syntax_isOfKind(v___x_3393_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec(v___x_3393_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v___x_3400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v_id_3402_; lean_object* v_binders_3403_; lean_object* v_type_3404_; lean_object* v_value_3405_; uint8_t v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___y_3419_; lean_object* v_id_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; uint8_t v___x_3496_; 
v___x_3401_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3393_);
lean_dec(v___x_3393_);
v_id_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_id_3402_);
v_binders_3403_ = lean_ctor_get(v___x_3401_, 1);
lean_inc_ref(v_binders_3403_);
v_type_3404_ = lean_ctor_get(v___x_3401_, 2);
lean_inc(v_type_3404_);
v_value_3405_ = lean_ctor_get(v___x_3401_, 3);
lean_inc(v_value_3405_);
lean_dec_ref(v___x_3401_);
v___x_3496_ = l_Lean_Syntax_isIdent(v_id_3402_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3402_, v___x_3390_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_id_3402_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref(v___x_3497_);
v_id_3478_ = v_a_3498_;
v___y_3479_ = v_a_3364_;
v___y_3480_ = v_a_3365_;
v___y_3481_ = v_a_3366_;
v___y_3482_ = v_a_3367_;
v___y_3483_ = v_a_3368_;
v___y_3484_ = v_a_3369_;
v___y_3485_ = v_a_3370_;
goto v___jp_3477_;
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_value_3405_);
lean_dec(v_type_3404_);
lean_dec_ref(v_binders_3403_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3499_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3497_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
v_id_3478_ = v_id_3402_;
v___y_3479_ = v_a_3364_;
v___y_3480_ = v_a_3365_;
v___y_3481_ = v_a_3366_;
v___y_3482_ = v_a_3367_;
v___y_3483_ = v_a_3368_;
v___y_3484_ = v_a_3369_;
v___y_3485_ = v_a_3370_;
goto v___jp_3477_;
}
v___jp_3406_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___f_3423_; lean_object* v___x_3424_; 
v___x_3420_ = lean_box(v___x_3390_);
v___x_3421_ = lean_box(v___x_3395_);
v___x_3422_ = lean_box(v___y_3419_);
v___f_3423_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3423_, 0, v_type_3404_);
lean_closure_set(v___f_3423_, 1, v_value_3405_);
lean_closure_set(v___f_3423_, 2, v___x_3420_);
lean_closure_set(v___f_3423_, 3, v___x_3421_);
lean_closure_set(v___f_3423_, 4, v___x_3392_);
lean_closure_set(v___f_3423_, 5, v___x_3422_);
v___x_3424_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3403_, v___f_3423_, v___y_3413_, v___y_3415_, v___y_3411_, v___y_3418_, v___y_3417_, v___y_3412_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v_options_3426_; lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3468_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v_options_3426_ = lean_ctor_get(v___y_3417_, 2);
v_fst_3427_ = lean_ctor_get(v_a_3425_, 0);
v_snd_3428_ = lean_ctor_get(v_a_3425_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3425_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3430_ = v_a_3425_;
v_isShared_3431_ = v_isSharedCheck_3468_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_inc(v_fst_3427_);
lean_dec(v_a_3425_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3468_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_inheritedTraceOptions_3432_; uint8_t v_hasTrace_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v_inheritedTraceOptions_3432_ = lean_ctor_get(v___y_3417_, 13);
v_hasTrace_3433_ = lean_ctor_get_uint8(v_options_3426_, sizeof(void*)*1);
v___x_3434_ = lean_box(v___y_3407_);
v___x_3435_ = lean_box(v___y_3409_);
v___x_3436_ = lean_box(v___x_3395_);
v___x_3437_ = lean_box(v___y_3419_);
v___x_3438_ = lean_box(v___x_3390_);
lean_inc(v_snd_3428_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3439_, 0, v___y_3408_);
lean_closure_set(v___f_3439_, 1, v___y_3410_);
lean_closure_set(v___f_3439_, 2, v_a_3377_);
lean_closure_set(v___f_3439_, 3, v___x_3434_);
lean_closure_set(v___f_3439_, 4, v___x_3435_);
lean_closure_set(v___f_3439_, 5, v___x_3436_);
lean_closure_set(v___f_3439_, 6, v_snd_3428_);
lean_closure_set(v___f_3439_, 7, v___x_3437_);
lean_closure_set(v___f_3439_, 8, v___x_3438_);
lean_closure_set(v___f_3439_, 9, v_letOrReassign_3360_);
lean_closure_set(v___f_3439_, 10, v_a_3374_);
v___x_3440_ = l_Lean_Syntax_getId(v___y_3416_);
lean_dec(v___y_3416_);
v___x_3441_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3440_);
if (v_hasTrace_3433_ == 0)
{
lean_object* v___x_3442_; 
lean_del_object(v___x_3430_);
v___x_3442_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3440_, v_fst_3427_, v_snd_3428_, v___f_3439_, v___y_3419_, v___x_3441_, v___y_3414_, v___y_3413_, v___y_3415_, v___y_3411_, v___y_3418_, v___y_3417_, v___y_3412_);
return v___x_3442_;
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3444_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3432_, v_options_3426_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
lean_del_object(v___x_3430_);
v___x_3446_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3440_, v_fst_3427_, v_snd_3428_, v___f_3439_, v___y_3419_, v___x_3441_, v___y_3414_, v___y_3413_, v___y_3415_, v___y_3411_, v___y_3418_, v___y_3417_, v___y_3412_);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_inc(v___x_3440_);
v___x_3447_ = l_Lean_MessageData_ofName(v___x_3440_);
v___x_3448_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 7);
lean_ctor_set(v___x_3430_, 1, v___x_3448_);
lean_ctor_set(v___x_3430_, 0, v___x_3447_);
v___x_3450_ = v___x_3430_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_inc(v_fst_3427_);
v___x_3451_ = l_Lean_MessageData_ofExpr(v_fst_3427_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
lean_inc(v_snd_3428_);
v___x_3455_ = l_Lean_MessageData_ofExpr(v_snd_3428_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3443_, v___x_3456_, v___y_3411_, v___y_3418_, v___y_3417_, v___y_3412_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3458_; 
lean_dec_ref(v___x_3457_);
v___x_3458_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3440_, v_fst_3427_, v_snd_3428_, v___f_3439_, v___y_3419_, v___x_3441_, v___y_3414_, v___y_3413_, v___y_3415_, v___y_3411_, v___y_3418_, v___y_3417_, v___y_3412_);
return v___x_3458_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v___x_3440_);
lean_dec_ref(v___f_3439_);
lean_dec(v_snd_3428_);
lean_dec(v_fst_3427_);
v_a_3459_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3457_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3457_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
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
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v___y_3416_);
lean_dec(v___y_3410_);
lean_dec(v___y_3408_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
v_a_3469_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3424_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3424_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
v___jp_3477_:
{
uint8_t v_nondep_3486_; 
v_nondep_3486_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1);
if (v_nondep_3486_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3360_) == 1)
{
uint8_t v_usedOnly_3487_; uint8_t v_zeta_3488_; lean_object* v_eq_x3f_3489_; 
v_usedOnly_3487_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 1);
v_zeta_3488_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 2);
v_eq_x3f_3489_ = lean_ctor_get(v_config_3359_, 0);
lean_inc(v_eq_x3f_3489_);
lean_dec_ref(v_config_3359_);
lean_inc(v_id_3478_);
v___y_3407_ = v_zeta_3488_;
v___y_3408_ = v_id_3478_;
v___y_3409_ = v_usedOnly_3487_;
v___y_3410_ = v_eq_x3f_3489_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3485_;
v___y_3413_ = v___y_3480_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v_id_3478_;
v___y_3417_ = v___y_3484_;
v___y_3418_ = v___y_3483_;
v___y_3419_ = v___x_3390_;
goto v___jp_3406_;
}
else
{
uint8_t v_usedOnly_3490_; uint8_t v_zeta_3491_; lean_object* v_eq_x3f_3492_; 
v_usedOnly_3490_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 1);
v_zeta_3491_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 2);
v_eq_x3f_3492_ = lean_ctor_get(v_config_3359_, 0);
lean_inc(v_eq_x3f_3492_);
lean_dec_ref(v_config_3359_);
lean_inc(v_id_3478_);
v___y_3407_ = v_zeta_3491_;
v___y_3408_ = v_id_3478_;
v___y_3409_ = v_usedOnly_3490_;
v___y_3410_ = v_eq_x3f_3492_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3485_;
v___y_3413_ = v___y_3480_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v_id_3478_;
v___y_3417_ = v___y_3484_;
v___y_3418_ = v___y_3483_;
v___y_3419_ = v_nondep_3486_;
goto v___jp_3406_;
}
}
else
{
uint8_t v_usedOnly_3493_; uint8_t v_zeta_3494_; lean_object* v_eq_x3f_3495_; 
v_usedOnly_3493_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 1);
v_zeta_3494_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*1 + 2);
v_eq_x3f_3495_ = lean_ctor_get(v_config_3359_, 0);
lean_inc(v_eq_x3f_3495_);
lean_dec_ref(v_config_3359_);
lean_inc(v_id_3478_);
v___y_3407_ = v_zeta_3494_;
v___y_3408_ = v_id_3478_;
v___y_3409_ = v_usedOnly_3493_;
v___y_3410_ = v_eq_x3f_3495_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3485_;
v___y_3413_ = v___y_3480_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v_id_3478_;
v___y_3417_ = v___y_3484_;
v___y_3418_ = v___y_3483_;
v___y_3419_ = v___x_3390_;
goto v___jp_3406_;
}
}
}
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3507_ = lean_unsigned_to_nat(1u);
v___x_3508_ = l_Lean_Syntax_getArg(v___x_3393_, v___x_3507_);
v___x_3509_ = l_Lean_Syntax_matchesNull(v___x_3508_, v___x_3392_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec(v___x_3393_);
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v___x_3510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v_rhs_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v_xType_x3f_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3511_ = lean_box(v___x_3395_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3512_, 0, v___x_3511_);
v___x_3513_ = l_Lean_Syntax_getArg(v___x_3393_, v___x_3392_);
v___x_3568_ = lean_unsigned_to_nat(2u);
v___x_3569_ = l_Lean_Syntax_getArg(v___x_3393_, v___x_3568_);
v___x_3570_ = l_Lean_Syntax_isNone(v___x_3569_);
if (v___x_3570_ == 0)
{
uint8_t v___x_3571_; 
lean_inc(v___x_3569_);
v___x_3571_ = l_Lean_Syntax_matchesNull(v___x_3569_, v___x_3507_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
lean_dec(v___x_3569_);
lean_dec(v___x_3513_);
lean_dec_ref(v___f_3512_);
lean_dec(v___x_3393_);
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v___x_3572_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3572_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = l_Lean_Syntax_getArg(v___x_3569_, v___x_3392_);
lean_dec(v___x_3569_);
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3573_);
v___x_3575_ = l_Lean_Syntax_isOfKind(v___x_3573_, v___x_3574_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
lean_dec(v___x_3573_);
lean_dec(v___x_3513_);
lean_dec_ref(v___f_3512_);
lean_dec(v___x_3393_);
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v___x_3576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = l_Lean_Syntax_getArg(v___x_3573_, v___x_3507_);
lean_dec(v___x_3573_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 1);
lean_ctor_set(v___x_3384_, 0, v___x_3577_);
v___x_3579_ = v___x_3384_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
v_xType_x3f_3534_ = v___x_3579_;
v___y_3535_ = v_a_3364_;
v___y_3536_ = v_a_3365_;
v___y_3537_ = v_a_3366_;
v___y_3538_ = v_a_3367_;
v___y_3539_ = v_a_3368_;
v___y_3540_ = v_a_3369_;
v___y_3541_ = v_a_3370_;
goto v___jp_3533_;
}
}
}
}
else
{
lean_object* v___x_3581_; 
lean_dec(v___x_3569_);
lean_del_object(v___x_3384_);
v___x_3581_ = lean_box(0);
v_xType_x3f_3534_ = v___x_3581_;
v___y_3535_ = v_a_3364_;
v___y_3536_ = v_a_3365_;
v___y_3537_ = v_a_3366_;
v___y_3538_ = v_a_3367_;
v___y_3539_ = v_a_3368_;
v___y_3540_ = v_a_3369_;
v___y_3541_ = v_a_3370_;
goto v___jp_3533_;
}
v___jp_3514_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___f_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3523_ = lean_box(v___x_3395_);
v___x_3524_ = lean_box(v___x_3390_);
lean_inc(v___x_3513_);
v___f_3525_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3525_, 0, v_rhs_3515_);
lean_closure_set(v___f_3525_, 1, v___x_3523_);
lean_closure_set(v___f_3525_, 2, v_config_3359_);
lean_closure_set(v___f_3525_, 3, v_a_3382_);
lean_closure_set(v___f_3525_, 4, v___x_3524_);
lean_closure_set(v___f_3525_, 5, v___x_3386_);
lean_closure_set(v___f_3525_, 6, v___x_3387_);
lean_closure_set(v___f_3525_, 7, v___x_3388_);
lean_closure_set(v___f_3525_, 8, v___f_3512_);
lean_closure_set(v___f_3525_, 9, v___x_3513_);
v___x_3526_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3526_, 0, v_a_3377_);
v___x_3527_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3527_, 0, v_letOrReassign_3360_);
lean_closure_set(v___x_3527_, 1, v_a_3374_);
lean_closure_set(v___x_3527_, 2, v___x_3526_);
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3529_ = l_Lean_MessageData_ofSyntax(v___x_3513_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = lean_box(0);
v___x_3532_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3530_, v___x_3527_, v___f_3525_, v___x_3531_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3532_;
}
v___jp_3533_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_unsigned_to_nat(4u);
v___x_3543_ = l_Lean_Syntax_getArg(v___x_3393_, v___x_3542_);
lean_dec(v___x_3393_);
if (lean_obj_tag(v_xType_x3f_3534_) == 0)
{
v_rhs_3515_ = v___x_3543_;
v___y_3516_ = v___y_3535_;
v___y_3517_ = v___y_3536_;
v___y_3518_ = v___y_3537_;
v___y_3519_ = v___y_3538_;
v___y_3520_ = v___y_3539_;
v___y_3521_ = v___y_3540_;
v___y_3522_ = v___y_3541_;
goto v___jp_3514_;
}
else
{
lean_object* v_val_3544_; lean_object* v_ref_3545_; lean_object* v_quotContext_3546_; lean_object* v_currMacroScope_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_val_3544_ = lean_ctor_get(v_xType_x3f_3534_, 0);
lean_inc(v_val_3544_);
lean_dec_ref(v_xType_x3f_3534_);
v_ref_3545_ = lean_ctor_get(v___y_3540_, 5);
v_quotContext_3546_ = lean_ctor_get(v___y_3540_, 10);
v_currMacroScope_3547_ = lean_ctor_get(v___y_3540_, 11);
v___x_3548_ = l_Lean_SourceInfo_fromRef(v_ref_3545_, v___x_3395_);
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3548_, 7);
v___x_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3548_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3554_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3555_ = lean_box(0);
lean_inc(v_currMacroScope_3547_);
lean_inc(v_quotContext_3546_);
v___x_3556_ = l_Lean_addMacroScope(v_quotContext_3546_, v___x_3555_, v_currMacroScope_3547_);
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3548_);
lean_ctor_set(v___x_3558_, 1, v___x_3554_);
lean_ctor_set(v___x_3558_, 2, v___x_3556_);
lean_ctor_set(v___x_3558_, 3, v___x_3557_);
v___x_3559_ = l_Lean_Syntax_node1(v___x_3548_, v___x_3553_, v___x_3558_);
v___x_3560_ = l_Lean_Syntax_node2(v___x_3548_, v___x_3550_, v___x_3552_, v___x_3559_);
v___x_3561_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3548_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3564_ = l_Lean_Syntax_node1(v___x_3548_, v___x_3563_, v_val_3544_);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3548_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_Syntax_node5(v___x_3548_, v___x_3549_, v___x_3560_, v___x_3543_, v___x_3562_, v___x_3564_, v___x_3566_);
v_rhs_3515_ = v___x_3567_;
v___y_3516_ = v___y_3535_;
v___y_3517_ = v___y_3536_;
v___y_3518_ = v___y_3537_;
v___y_3519_ = v___y_3538_;
v___y_3520_ = v___y_3539_;
v___y_3521_ = v___y_3540_;
v___y_3522_ = v___y_3541_;
goto v___jp_3514_;
}
}
}
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_del_object(v___x_3384_);
lean_dec(v_a_3382_);
lean_dec(v_a_3374_);
v___x_3582_ = lean_box(v___x_3390_);
lean_inc(v___x_3393_);
v___x_3583_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3583_, 0, v___x_3393_);
lean_closure_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3583_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v_ref_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___x_3584_);
v_ref_3586_ = lean_ctor_get(v_a_3369_, 5);
v___x_3587_ = 0;
v___x_3588_ = l_Lean_SourceInfo_fromRef(v_ref_3586_, v___x_3587_);
v___x_3589_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3389_, v_a_3585_);
lean_inc(v___x_3589_);
v___x_3590_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3590_, 0, v_config_3359_);
lean_closure_set(v___x_3590_, 1, v_letOrReassign_3360_);
lean_closure_set(v___x_3590_, 2, v___x_3589_);
lean_closure_set(v___x_3590_, 3, v_tk_3362_);
lean_closure_set(v___x_3590_, 4, v_a_3377_);
v___x_3591_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3393_, v___x_3589_, v___x_3590_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
return v___x_3591_;
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v___x_3393_);
lean_dec(v_a_3377_);
lean_dec(v_tk_3362_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3592_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3584_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3584_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3379_);
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_tk_3362_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
return v___x_3381_;
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v_a_3377_);
lean_dec(v_a_3374_);
lean_dec(v_tk_3362_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3601_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3378_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3378_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3374_);
lean_dec(v_tk_3362_);
lean_dec(v_decl_3361_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3609_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3376_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3376_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_a_3374_);
lean_dec_ref(v_dec_3363_);
lean_dec(v_tk_3362_);
lean_dec(v_decl_3361_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3617_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3375_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3375_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v_dec_3363_);
lean_dec(v_tk_3362_);
lean_dec(v_decl_3361_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3625_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3373_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3373_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v_dec_3363_);
lean_dec(v_tk_3362_);
lean_dec(v_decl_3361_);
lean_dec(v_letOrReassign_3360_);
lean_dec_ref(v_config_3359_);
v_a_3633_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3372_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3372_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3642_, v_x_3643_, v_x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3646_, lean_object* v_msg_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3646_, v_msg_3647_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3657_, lean_object* v_msg_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3657_, v_msg_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec_ref(v___y_3659_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3673_, v___y_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec_ref(v___y_3677_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3686_, lean_object* v_beforeStx_3687_, lean_object* v_afterStx_3688_, lean_object* v_x_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3687_, v_afterStx_3688_, v_x_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3699_, lean_object* v_beforeStx_3700_, lean_object* v_afterStx_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3699_, v_beforeStx_3700_, v_afterStx_3701_, v_x_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v___y_3703_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3713_, v___y_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3717_, lean_object* v_x_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3717_, v_x_3718_, v___y_3719_, v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v_x_3718_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3722_, lean_object* v_ref_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3723_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_ref_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3733_, v_ref_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3744_, lean_object* v_x_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3755_, lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3755_, v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3766_, lean_object* v_x_3767_, size_t v_x_3768_, size_t v_x_3769_, lean_object* v_x_3770_, lean_object* v_x_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3767_, v_x_3768_, v_x_3769_, v_x_3770_, v_x_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
size_t v_x_102651__boxed_3779_; size_t v_x_102652__boxed_3780_; lean_object* v_res_3781_; 
v_x_102651__boxed_3779_ = lean_unbox_usize(v_x_3775_);
lean_dec(v_x_3775_);
v_x_102652__boxed_3780_ = lean_unbox_usize(v_x_3776_);
lean_dec(v_x_3776_);
v_res_3781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3773_, v_x_3774_, v_x_102651__boxed_3779_, v_x_102652__boxed_3780_, v_x_3777_, v_x_3778_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3782_, lean_object* v_stx_3783_, lean_object* v_output_3784_, lean_object* v_x_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3783_, v_output_3784_, v_x_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3794_, lean_object* v_stx_3795_, lean_object* v_output_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3794_, v_stx_3795_, v_output_3796_, v_x_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3806_, lean_object* v_as_x27_3807_, lean_object* v_b_3808_, lean_object* v_a_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3807_, v_b_3808_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3819_, lean_object* v_as_x27_3820_, lean_object* v_b_3821_, lean_object* v_a_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3819_, v_as_x27_3820_, v_b_3821_, v_a_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v_as_x27_3820_);
lean_dec(v_as_3819_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3832_, lean_object* v_ref_3833_, lean_object* v_msg_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3833_, v_msg_3834_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_msg_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3844_, v_ref_3845_, v_msg_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v_ref_3845_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3856_, lean_object* v_n_3857_, lean_object* v_k_3858_, lean_object* v_v_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3857_, v_k_3858_, v_v_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3861_, size_t v_depth_3862_, lean_object* v_keys_3863_, lean_object* v_vals_3864_, lean_object* v_heq_3865_, lean_object* v_i_3866_, lean_object* v_entries_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3862_, v_keys_3863_, v_vals_3864_, v_i_3866_, v_entries_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3869_, lean_object* v_depth_3870_, lean_object* v_keys_3871_, lean_object* v_vals_3872_, lean_object* v_heq_3873_, lean_object* v_i_3874_, lean_object* v_entries_3875_){
_start:
{
size_t v_depth_boxed_3876_; lean_object* v_res_3877_; 
v_depth_boxed_3876_ = lean_unbox_usize(v_depth_3870_);
lean_dec(v_depth_3870_);
v_res_3877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3869_, v_depth_boxed_3876_, v_keys_3871_, v_vals_3872_, v_heq_3873_, v_i_3874_, v_entries_3875_);
lean_dec_ref(v_vals_3872_);
lean_dec_ref(v_keys_3871_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3894_, lean_object* v_x_3895_, lean_object* v_mkInfoTree_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3895_, v_mkInfoTree_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3905_, lean_object* v_x_3906_, lean_object* v_mkInfoTree_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3905_, v_x_3906_, v_mkInfoTree_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_, lean_object* v_x_3920_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3917_, v_x_3918_, v_x_3919_, v_x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_){
_start:
{
uint8_t v___x_3925_; 
v___x_3925_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3923_, v_x_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_){
_start:
{
uint8_t v_res_3929_; lean_object* v_r_3930_; 
v_res_3929_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3926_, v_x_3927_, v_x_3928_);
lean_dec_ref(v_x_3928_);
lean_dec_ref(v_x_3927_);
v_r_3930_ = lean_box(v_res_3929_);
return v_r_3930_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3931_, lean_object* v_x_3932_, size_t v_x_3933_, lean_object* v_x_3934_){
_start:
{
uint8_t v___x_3935_; 
v___x_3935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3932_, v_x_3933_, v_x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3936_, lean_object* v_x_3937_, lean_object* v_x_3938_, lean_object* v_x_3939_){
_start:
{
size_t v_x_102814__boxed_3940_; uint8_t v_res_3941_; lean_object* v_r_3942_; 
v_x_102814__boxed_3940_ = lean_unbox_usize(v_x_3938_);
lean_dec(v_x_3938_);
v_res_3941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3936_, v_x_3937_, v_x_102814__boxed_3940_, v_x_3939_);
lean_dec_ref(v_x_3939_);
lean_dec_ref(v_x_3937_);
v_r_3942_ = lean_box(v_res_3941_);
return v_r_3942_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27(lean_object* v_00_u03b2_3943_, lean_object* v_keys_3944_, lean_object* v_vals_3945_, lean_object* v_heq_3946_, lean_object* v_i_3947_, lean_object* v_k_3948_){
_start:
{
uint8_t v___x_3949_; 
v___x_3949_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_keys_3944_, v_i_3947_, v_k_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___boxed(lean_object* v_00_u03b2_3950_, lean_object* v_keys_3951_, lean_object* v_vals_3952_, lean_object* v_heq_3953_, lean_object* v_i_3954_, lean_object* v_k_3955_){
_start:
{
uint8_t v_res_3956_; lean_object* v_r_3957_; 
v_res_3956_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27(v_00_u03b2_3950_, v_keys_3951_, v_vals_3952_, v_heq_3953_, v_i_3954_, v_k_3955_);
lean_dec_ref(v_k_3955_);
lean_dec_ref(v_vals_3952_);
lean_dec_ref(v_keys_3951_);
v_r_3957_ = lean_box(v_res_3956_);
return v_r_3957_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3967_, lean_object* v_otherwise_x3f_3968_, uint8_t v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v___x_3972_, lean_object* v___x_3973_, lean_object* v___x_3974_, lean_object* v_dec_3975_, uint8_t v___x_3976_, lean_object* v___y_3977_, lean_object* v___x_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; uint8_t v___y_4010_; 
switch(lean_obj_tag(v_letOrReassign_3967_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3968_) == 1)
{
lean_object* v_mutTk_x3f_4021_; lean_object* v_val_4022_; lean_object* v_ref_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4053_; 
v_mutTk_x3f_4021_ = lean_ctor_get(v_letOrReassign_3967_, 0);
v_val_4022_ = lean_ctor_get(v_otherwise_x3f_3968_, 0);
lean_inc(v_val_4022_);
lean_dec_ref(v_otherwise_x3f_3968_);
v_ref_4023_ = lean_ctor_get(v___y_3984_, 5);
v___x_4024_ = l_Lean_SourceInfo_fromRef(v_ref_4023_, v___x_3969_);
v___x_4025_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3972_);
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
v___x_4026_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4025_);
v___x_4027_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4024_);
v___x_4028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4024_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4030_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4021_) == 1)
{
lean_object* v_val_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_val_4068_ = lean_ctor_get(v_mutTk_x3f_4021_, 0);
v___x_4069_ = l_Lean_SourceInfo_fromRef(v_val_4068_, v___x_3976_);
v___x_4070_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = l_Array_mkArray1___redArg(v___x_4071_);
v___y_4053_ = v___x_4072_;
goto v___jp_4052_;
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_3978_);
v___y_4053_ = v___x_4073_;
goto v___jp_4052_;
}
v___jp_4031_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4037_ = l_Array_append___redArg(v___x_4030_, v___y_4036_);
lean_dec_ref(v___y_4036_);
lean_inc(v___x_4024_);
v___x_4038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4024_);
lean_ctor_set(v___x_4038_, 1, v___x_4029_);
lean_ctor_set(v___x_4038_, 2, v___x_4037_);
v___x_4039_ = lean_unsigned_to_nat(9u);
v___x_4040_ = lean_mk_empty_array_with_capacity(v___x_4039_);
v___x_4041_ = lean_array_push(v___x_4040_, v___x_4028_);
v___x_4042_ = lean_array_push(v___x_4041_, v___y_4032_);
v___x_4043_ = lean_array_push(v___x_4042_, v___y_4034_);
v___x_4044_ = lean_array_push(v___x_4043_, v___x_3973_);
v___x_4045_ = lean_array_push(v___x_4044_, v___y_4033_);
v___x_4046_ = lean_array_push(v___x_4045_, v___x_3974_);
v___x_4047_ = lean_array_push(v___x_4046_, v___y_4035_);
v___x_4048_ = lean_array_push(v___x_4047_, v_val_4022_);
v___x_4049_ = lean_array_push(v___x_4048_, v___x_4038_);
v___x_4050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4024_);
lean_ctor_set(v___x_4050_, 1, v___x_4026_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
v___x_4051_ = l_Lean_Elab_Do_elabDoElem(v___x_4050_, v_dec_3975_, v___x_3976_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_4051_;
}
v___jp_4052_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4054_ = l_Array_append___redArg(v___x_4030_, v___y_4053_);
lean_dec_ref(v___y_4053_);
lean_inc_n(v___x_4024_, 5);
v___x_4055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4024_);
lean_ctor_set(v___x_4055_, 1, v___x_4029_);
lean_ctor_set(v___x_4055_, 2, v___x_4054_);
v___x_4056_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4057_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4056_);
v___x_4058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4024_);
lean_ctor_set(v___x_4058_, 1, v___x_4029_);
lean_ctor_set(v___x_4058_, 2, v___x_4030_);
v___x_4059_ = l_Lean_Syntax_node1(v___x_4024_, v___x_4057_, v___x_4058_);
v___x_4060_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4024_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4024_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
if (lean_obj_tag(v___y_3977_) == 0)
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_mk_empty_array_with_capacity(v___x_3978_);
v___y_4032_ = v___x_4055_;
v___y_4033_ = v___x_4061_;
v___y_4034_ = v___x_4059_;
v___y_4035_ = v___x_4063_;
v___y_4036_ = v___x_4064_;
goto v___jp_4031_;
}
else
{
lean_object* v_val_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_val_4065_ = lean_ctor_get(v___y_3977_, 0);
lean_inc(v_val_4065_);
lean_dec_ref(v___y_3977_);
v___x_4066_ = lean_mk_empty_array_with_capacity(v___x_3978_);
v___x_4067_ = lean_array_push(v___x_4066_, v_val_4065_);
v___y_4032_ = v___x_4055_;
v___y_4033_ = v___x_4061_;
v___y_4034_ = v___x_4059_;
v___y_4035_ = v___x_4063_;
v___y_4036_ = v___x_4067_;
goto v___jp_4031_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4074_; lean_object* v_ref_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___y_4084_; 
lean_dec(v___y_3977_);
lean_dec(v_otherwise_x3f_3968_);
v_mutTk_x3f_4074_ = lean_ctor_get(v_letOrReassign_3967_, 0);
v_ref_4075_ = lean_ctor_get(v___y_3984_, 5);
v___x_4076_ = l_Lean_SourceInfo_fromRef(v_ref_4075_, v___x_3969_);
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3972_);
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
v___x_4078_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4077_);
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4076_);
v___x_4080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4076_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4082_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4074_) == 1)
{
lean_object* v_val_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_val_4101_ = lean_ctor_get(v_mutTk_x3f_4074_, 0);
v___x_4102_ = l_Lean_SourceInfo_fromRef(v_val_4101_, v___x_3976_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Array_mkArray1___redArg(v___x_4104_);
v___y_4084_ = v___x_4105_;
goto v___jp_4083_;
}
else
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_mk_empty_array_with_capacity(v___x_3978_);
v___y_4084_ = v___x_4106_;
goto v___jp_4083_;
}
v___jp_4083_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4085_ = l_Array_append___redArg(v___x_4082_, v___y_4084_);
lean_dec_ref(v___y_4084_);
lean_inc_n(v___x_4076_, 6);
v___x_4086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4076_);
lean_ctor_set(v___x_4086_, 1, v___x_4081_);
lean_ctor_set(v___x_4086_, 2, v___x_4085_);
v___x_4087_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3972_, 2);
lean_inc_ref_n(v___x_3971_, 2);
lean_inc_ref_n(v___x_3970_, 2);
v___x_4088_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4087_);
v___x_4089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4076_);
lean_ctor_set(v___x_4089_, 1, v___x_4081_);
lean_ctor_set(v___x_4089_, 2, v___x_4082_);
lean_inc_ref_n(v___x_4089_, 2);
v___x_4090_ = l_Lean_Syntax_node1(v___x_4076_, v___x_4088_, v___x_4089_);
v___x_4091_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4092_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4091_);
v___x_4093_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4094_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4093_);
v___x_4095_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4076_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = l_Lean_Syntax_node5(v___x_4076_, v___x_4094_, v___x_3973_, v___x_4089_, v___x_4089_, v___x_4096_, v___x_3974_);
v___x_4098_ = l_Lean_Syntax_node1(v___x_4076_, v___x_4092_, v___x_4097_);
v___x_4099_ = l_Lean_Syntax_node4(v___x_4076_, v___x_4078_, v___x_4080_, v___x_4086_, v___x_4090_, v___x_4098_);
v___x_4100_ = l_Lean_Elab_Do_elabDoElem(v___x_4099_, v_dec_3975_, v___x_3976_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_4100_;
}
}
}
case 1:
{
lean_dec(v___y_3977_);
if (lean_obj_tag(v_otherwise_x3f_3968_) == 1)
{
lean_object* v___x_4107_; 
lean_dec_ref(v_otherwise_x3f_3968_);
lean_dec_ref(v_dec_3975_);
lean_dec(v___x_3974_);
lean_dec(v___x_3973_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
v___x_4107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4107_;
}
else
{
lean_object* v_ref_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec(v_otherwise_x3f_3968_);
v_ref_4108_ = lean_ctor_get(v___y_3984_, 5);
v___x_4109_ = l_Lean_SourceInfo_fromRef(v_ref_4108_, v___x_3969_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3972_, 3);
lean_inc_ref_n(v___x_3971_, 3);
lean_inc_ref_n(v___x_3970_, 3);
v___x_4111_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4110_);
v___x_4112_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4109_, 6);
v___x_4113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4109_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4115_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4114_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4117_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4109_);
lean_ctor_set(v___x_4118_, 1, v___x_4116_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
lean_inc_ref_n(v___x_4118_, 2);
v___x_4119_ = l_Lean_Syntax_node1(v___x_4109_, v___x_4115_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4121_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4120_);
v___x_4122_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4123_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_4122_);
v___x_4124_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4109_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_Syntax_node5(v___x_4109_, v___x_4123_, v___x_3973_, v___x_4118_, v___x_4118_, v___x_4125_, v___x_3974_);
v___x_4127_ = l_Lean_Syntax_node1(v___x_4109_, v___x_4121_, v___x_4126_);
v___x_4128_ = l_Lean_Syntax_node3(v___x_4109_, v___x_4111_, v___x_4113_, v___x_4119_, v___x_4127_);
v___x_4129_ = l_Lean_Elab_Do_elabDoElem(v___x_4128_, v_dec_3975_, v___x_3976_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_4129_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3968_);
if (lean_obj_tag(v___y_3977_) == 0)
{
v___y_4010_ = v___x_3976_;
goto v___jp_4009_;
}
else
{
lean_dec_ref(v___y_3977_);
v___y_4010_ = v___x_3969_;
goto v___jp_4009_;
}
}
}
v___jp_3987_:
{
lean_object* v_ref_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_ref_3995_ = lean_ctor_get(v___y_3993_, 5);
v___x_3996_ = l_Lean_SourceInfo_fromRef(v_ref_3995_, v___x_3969_);
v___x_3997_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3972_);
lean_inc_ref(v___x_3971_);
lean_inc_ref(v___x_3970_);
v___x_3998_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_3997_);
v___x_3999_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4000_ = l_Lean_Name_mkStr4(v___x_3970_, v___x_3971_, v___x_3972_, v___x_3999_);
v___x_4001_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4002_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3996_, 3);
v___x_4003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3996_);
lean_ctor_set(v___x_4003_, 1, v___x_4001_);
lean_ctor_set(v___x_4003_, 2, v___x_4002_);
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_3996_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
lean_inc_ref(v___x_4003_);
v___x_4006_ = l_Lean_Syntax_node5(v___x_3996_, v___x_4000_, v___x_3973_, v___x_4003_, v___x_4003_, v___x_4005_, v___x_3974_);
v___x_4007_ = l_Lean_Syntax_node1(v___x_3996_, v___x_3998_, v___x_4006_);
v___x_4008_ = l_Lean_Elab_Do_elabDoElem(v___x_4007_, v_dec_3975_, v___x_3976_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v___x_4008_;
}
v___jp_4009_:
{
if (v___y_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec_ref(v_dec_3975_);
lean_dec(v___x_3974_);
lean_dec(v___x_3973_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
v___x_4011_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4012_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4011_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
v___y_3988_ = v___y_3979_;
v___y_3989_ = v___y_3980_;
v___y_3990_ = v___y_3981_;
v___y_3991_ = v___y_3982_;
v___y_3992_ = v___y_3983_;
v___y_3993_ = v___y_3984_;
v___y_3994_ = v___y_3985_;
goto v___jp_3987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4130_ = _args[0];
lean_object* v_otherwise_x3f_4131_ = _args[1];
lean_object* v___x_4132_ = _args[2];
lean_object* v___x_4133_ = _args[3];
lean_object* v___x_4134_ = _args[4];
lean_object* v___x_4135_ = _args[5];
lean_object* v___x_4136_ = _args[6];
lean_object* v___x_4137_ = _args[7];
lean_object* v_dec_4138_ = _args[8];
lean_object* v___x_4139_ = _args[9];
lean_object* v___y_4140_ = _args[10];
lean_object* v___x_4141_ = _args[11];
lean_object* v___y_4142_ = _args[12];
lean_object* v___y_4143_ = _args[13];
lean_object* v___y_4144_ = _args[14];
lean_object* v___y_4145_ = _args[15];
lean_object* v___y_4146_ = _args[16];
lean_object* v___y_4147_ = _args[17];
lean_object* v___y_4148_ = _args[18];
lean_object* v___y_4149_ = _args[19];
_start:
{
uint8_t v___x_39001__boxed_4150_; uint8_t v___x_39007__boxed_4151_; lean_object* v_res_4152_; 
v___x_39001__boxed_4150_ = lean_unbox(v___x_4132_);
v___x_39007__boxed_4151_ = lean_unbox(v___x_4139_);
v_res_4152_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4130_, v_otherwise_x3f_4131_, v___x_39001__boxed_4150_, v___x_4133_, v___x_4134_, v___x_4135_, v___x_4136_, v___x_4137_, v_dec_4138_, v___x_39007__boxed_4151_, v___y_4140_, v___x_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___x_4141_);
lean_dec(v_letOrReassign_4130_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4153_, lean_object* v_otherwise_x3f_4154_, uint8_t v___x_4155_, lean_object* v___x_4156_, lean_object* v___x_4157_, lean_object* v___x_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v_dec_4161_, uint8_t v___x_4162_, lean_object* v___y_4163_, lean_object* v___x_4164_, uint8_t v___x_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; uint8_t v___y_4197_; 
switch(lean_obj_tag(v_letOrReassign_4153_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4154_) == 1)
{
lean_object* v_mutTk_x3f_4208_; lean_object* v_val_4209_; lean_object* v_ref_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4240_; 
v_mutTk_x3f_4208_ = lean_ctor_get(v_letOrReassign_4153_, 0);
v_val_4209_ = lean_ctor_get(v_otherwise_x3f_4154_, 0);
lean_inc(v_val_4209_);
lean_dec_ref(v_otherwise_x3f_4154_);
v_ref_4210_ = lean_ctor_get(v___y_4171_, 5);
v___x_4211_ = l_Lean_SourceInfo_fromRef(v_ref_4210_, v___x_4155_);
v___x_4212_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4158_);
lean_inc_ref(v___x_4157_);
lean_inc_ref(v___x_4156_);
v___x_4213_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4212_);
v___x_4214_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4211_);
v___x_4215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4211_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4217_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4208_) == 1)
{
lean_object* v_val_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_val_4255_ = lean_ctor_get(v_mutTk_x3f_4208_, 0);
v___x_4256_ = l_Lean_SourceInfo_fromRef(v_val_4255_, v___x_4162_);
v___x_4257_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l_Array_mkArray1___redArg(v___x_4258_);
v___y_4240_ = v___x_4259_;
goto v___jp_4239_;
}
else
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___y_4240_ = v___x_4260_;
goto v___jp_4239_;
}
v___jp_4218_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4224_ = l_Array_append___redArg(v___x_4217_, v___y_4223_);
lean_dec_ref(v___y_4223_);
lean_inc(v___x_4211_);
v___x_4225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4211_);
lean_ctor_set(v___x_4225_, 1, v___x_4216_);
lean_ctor_set(v___x_4225_, 2, v___x_4224_);
v___x_4226_ = lean_unsigned_to_nat(9u);
v___x_4227_ = lean_mk_empty_array_with_capacity(v___x_4226_);
v___x_4228_ = lean_array_push(v___x_4227_, v___x_4215_);
v___x_4229_ = lean_array_push(v___x_4228_, v___y_4222_);
v___x_4230_ = lean_array_push(v___x_4229_, v___y_4220_);
v___x_4231_ = lean_array_push(v___x_4230_, v___x_4159_);
v___x_4232_ = lean_array_push(v___x_4231_, v___y_4219_);
v___x_4233_ = lean_array_push(v___x_4232_, v___x_4160_);
v___x_4234_ = lean_array_push(v___x_4233_, v___y_4221_);
v___x_4235_ = lean_array_push(v___x_4234_, v_val_4209_);
v___x_4236_ = lean_array_push(v___x_4235_, v___x_4225_);
v___x_4237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4211_);
lean_ctor_set(v___x_4237_, 1, v___x_4213_);
lean_ctor_set(v___x_4237_, 2, v___x_4236_);
v___x_4238_ = l_Lean_Elab_Do_elabDoElem(v___x_4237_, v_dec_4161_, v___x_4162_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4238_;
}
v___jp_4239_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4241_ = l_Array_append___redArg(v___x_4217_, v___y_4240_);
lean_dec_ref(v___y_4240_);
lean_inc_n(v___x_4211_, 5);
v___x_4242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4211_);
lean_ctor_set(v___x_4242_, 1, v___x_4216_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
v___x_4243_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4244_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4243_);
v___x_4245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4211_);
lean_ctor_set(v___x_4245_, 1, v___x_4216_);
lean_ctor_set(v___x_4245_, 2, v___x_4217_);
v___x_4246_ = l_Lean_Syntax_node1(v___x_4211_, v___x_4244_, v___x_4245_);
v___x_4247_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4211_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4211_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
if (lean_obj_tag(v___y_4163_) == 0)
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___y_4219_ = v___x_4248_;
v___y_4220_ = v___x_4246_;
v___y_4221_ = v___x_4250_;
v___y_4222_ = v___x_4242_;
v___y_4223_ = v___x_4251_;
goto v___jp_4218_;
}
else
{
lean_object* v_val_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v_val_4252_ = lean_ctor_get(v___y_4163_, 0);
lean_inc(v_val_4252_);
lean_dec_ref(v___y_4163_);
v___x_4253_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___x_4254_ = lean_array_push(v___x_4253_, v_val_4252_);
v___y_4219_ = v___x_4248_;
v___y_4220_ = v___x_4246_;
v___y_4221_ = v___x_4250_;
v___y_4222_ = v___x_4242_;
v___y_4223_ = v___x_4254_;
goto v___jp_4218_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4261_; lean_object* v_ref_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___y_4271_; 
lean_dec(v___y_4163_);
lean_dec(v_otherwise_x3f_4154_);
v_mutTk_x3f_4261_ = lean_ctor_get(v_letOrReassign_4153_, 0);
v_ref_4262_ = lean_ctor_get(v___y_4171_, 5);
v___x_4263_ = l_Lean_SourceInfo_fromRef(v_ref_4262_, v___x_4155_);
v___x_4264_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4158_);
lean_inc_ref(v___x_4157_);
lean_inc_ref(v___x_4156_);
v___x_4265_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4264_);
v___x_4266_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4263_);
v___x_4267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4263_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4269_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4261_) == 1)
{
lean_object* v_val_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_val_4288_ = lean_ctor_get(v_mutTk_x3f_4261_, 0);
v___x_4289_ = l_Lean_SourceInfo_fromRef(v_val_4288_, v___x_4162_);
v___x_4290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = l_Array_mkArray1___redArg(v___x_4291_);
v___y_4271_ = v___x_4292_;
goto v___jp_4270_;
}
else
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_mk_empty_array_with_capacity(v___x_4164_);
v___y_4271_ = v___x_4293_;
goto v___jp_4270_;
}
v___jp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4272_ = l_Array_append___redArg(v___x_4269_, v___y_4271_);
lean_dec_ref(v___y_4271_);
lean_inc_n(v___x_4263_, 6);
v___x_4273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4263_);
lean_ctor_set(v___x_4273_, 1, v___x_4268_);
lean_ctor_set(v___x_4273_, 2, v___x_4272_);
v___x_4274_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4158_, 2);
lean_inc_ref_n(v___x_4157_, 2);
lean_inc_ref_n(v___x_4156_, 2);
v___x_4275_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4274_);
v___x_4276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4263_);
lean_ctor_set(v___x_4276_, 1, v___x_4268_);
lean_ctor_set(v___x_4276_, 2, v___x_4269_);
lean_inc_ref_n(v___x_4276_, 2);
v___x_4277_ = l_Lean_Syntax_node1(v___x_4263_, v___x_4275_, v___x_4276_);
v___x_4278_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4279_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4278_);
v___x_4280_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4281_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4280_);
v___x_4282_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4263_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = l_Lean_Syntax_node5(v___x_4263_, v___x_4281_, v___x_4159_, v___x_4276_, v___x_4276_, v___x_4283_, v___x_4160_);
v___x_4285_ = l_Lean_Syntax_node1(v___x_4263_, v___x_4279_, v___x_4284_);
v___x_4286_ = l_Lean_Syntax_node4(v___x_4263_, v___x_4265_, v___x_4267_, v___x_4273_, v___x_4277_, v___x_4285_);
v___x_4287_ = l_Lean_Elab_Do_elabDoElem(v___x_4286_, v_dec_4161_, v___x_4162_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4287_;
}
}
}
case 1:
{
lean_dec(v___y_4163_);
if (lean_obj_tag(v_otherwise_x3f_4154_) == 1)
{
lean_object* v___x_4294_; 
lean_dec_ref(v_otherwise_x3f_4154_);
lean_dec_ref(v_dec_4161_);
lean_dec(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec_ref(v___x_4158_);
lean_dec_ref(v___x_4157_);
lean_dec_ref(v___x_4156_);
v___x_4294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4294_;
}
else
{
lean_object* v_ref_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
lean_dec(v_otherwise_x3f_4154_);
v_ref_4295_ = lean_ctor_get(v___y_4171_, 5);
v___x_4296_ = l_Lean_SourceInfo_fromRef(v_ref_4295_, v___x_4155_);
v___x_4297_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4158_, 3);
lean_inc_ref_n(v___x_4157_, 3);
lean_inc_ref_n(v___x_4156_, 3);
v___x_4298_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4297_);
v___x_4299_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4296_, 6);
v___x_4300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4296_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4302_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4301_);
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4304_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4296_);
lean_ctor_set(v___x_4305_, 1, v___x_4303_);
lean_ctor_set(v___x_4305_, 2, v___x_4304_);
lean_inc_ref_n(v___x_4305_, 2);
v___x_4306_ = l_Lean_Syntax_node1(v___x_4296_, v___x_4302_, v___x_4305_);
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4308_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4307_);
v___x_4309_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4310_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4309_);
v___x_4311_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4296_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = l_Lean_Syntax_node5(v___x_4296_, v___x_4310_, v___x_4159_, v___x_4305_, v___x_4305_, v___x_4312_, v___x_4160_);
v___x_4314_ = l_Lean_Syntax_node1(v___x_4296_, v___x_4308_, v___x_4313_);
v___x_4315_ = l_Lean_Syntax_node3(v___x_4296_, v___x_4298_, v___x_4300_, v___x_4306_, v___x_4314_);
v___x_4316_ = l_Lean_Elab_Do_elabDoElem(v___x_4315_, v_dec_4161_, v___x_4162_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
return v___x_4316_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4154_);
if (lean_obj_tag(v___y_4163_) == 0)
{
v___y_4197_ = v___x_4165_;
goto v___jp_4196_;
}
else
{
lean_dec_ref(v___y_4163_);
v___y_4197_ = v___x_4155_;
goto v___jp_4196_;
}
}
}
v___jp_4174_:
{
lean_object* v_ref_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_ref_4182_ = lean_ctor_get(v___y_4180_, 5);
v___x_4183_ = l_Lean_SourceInfo_fromRef(v_ref_4182_, v___x_4155_);
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4158_);
lean_inc_ref(v___x_4157_);
lean_inc_ref(v___x_4156_);
v___x_4185_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4184_);
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4187_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4186_);
v___x_4188_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4189_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4183_, 3);
v___x_4190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4183_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
lean_ctor_set(v___x_4190_, 2, v___x_4189_);
v___x_4191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4183_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
lean_inc_ref(v___x_4190_);
v___x_4193_ = l_Lean_Syntax_node5(v___x_4183_, v___x_4187_, v___x_4159_, v___x_4190_, v___x_4190_, v___x_4192_, v___x_4160_);
v___x_4194_ = l_Lean_Syntax_node1(v___x_4183_, v___x_4185_, v___x_4193_);
v___x_4195_ = l_Lean_Elab_Do_elabDoElem(v___x_4194_, v_dec_4161_, v___x_4162_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
return v___x_4195_;
}
v___jp_4196_:
{
if (v___y_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v_dec_4161_);
lean_dec(v___x_4160_);
lean_dec(v___x_4159_);
lean_dec_ref(v___x_4158_);
lean_dec_ref(v___x_4157_);
lean_dec_ref(v___x_4156_);
v___x_4198_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4199_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4198_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
else
{
v___y_4175_ = v___y_4166_;
v___y_4176_ = v___y_4167_;
v___y_4177_ = v___y_4168_;
v___y_4178_ = v___y_4169_;
v___y_4179_ = v___y_4170_;
v___y_4180_ = v___y_4171_;
v___y_4181_ = v___y_4172_;
goto v___jp_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4317_ = _args[0];
lean_object* v_otherwise_x3f_4318_ = _args[1];
lean_object* v___x_4319_ = _args[2];
lean_object* v___x_4320_ = _args[3];
lean_object* v___x_4321_ = _args[4];
lean_object* v___x_4322_ = _args[5];
lean_object* v___x_4323_ = _args[6];
lean_object* v___x_4324_ = _args[7];
lean_object* v_dec_4325_ = _args[8];
lean_object* v___x_4326_ = _args[9];
lean_object* v___y_4327_ = _args[10];
lean_object* v___x_4328_ = _args[11];
lean_object* v___x_4329_ = _args[12];
lean_object* v___y_4330_ = _args[13];
lean_object* v___y_4331_ = _args[14];
lean_object* v___y_4332_ = _args[15];
lean_object* v___y_4333_ = _args[16];
lean_object* v___y_4334_ = _args[17];
lean_object* v___y_4335_ = _args[18];
lean_object* v___y_4336_ = _args[19];
lean_object* v___y_4337_ = _args[20];
_start:
{
uint8_t v___x_39383__boxed_4338_; uint8_t v___x_39389__boxed_4339_; uint8_t v___x_39392__boxed_4340_; lean_object* v_res_4341_; 
v___x_39383__boxed_4338_ = lean_unbox(v___x_4319_);
v___x_39389__boxed_4339_ = lean_unbox(v___x_4326_);
v___x_39392__boxed_4340_ = lean_unbox(v___x_4329_);
v_res_4341_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4317_, v_otherwise_x3f_4318_, v___x_39383__boxed_4338_, v___x_4320_, v___x_4321_, v___x_4322_, v___x_4323_, v___x_4324_, v_dec_4325_, v___x_39389__boxed_4339_, v___y_4327_, v___x_4328_, v___x_39392__boxed_4340_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___x_4328_);
lean_dec(v_letOrReassign_4317_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4362_, lean_object* v_stx_4363_, lean_object* v_tk_4364_, lean_object* v_dec_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4375_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4363_);
v___x_4378_ = l_Lean_Syntax_isOfKind(v_stx_4363_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4363_);
v___x_4380_ = l_Lean_Syntax_isOfKind(v_stx_4363_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; 
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; 
v___x_4382_ = lean_unsigned_to_nat(0u);
v___x_4383_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4382_);
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4383_);
v___x_4385_ = l_Lean_Syntax_isOfKind(v___x_4383_, v___x_4384_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4471_; lean_object* v_patType_x3f_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4502_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4471_);
v___x_4503_ = l_Lean_Syntax_isNone(v___x_4502_);
if (v___x_4503_ == 0)
{
uint8_t v___x_4504_; 
lean_inc(v___x_4502_);
v___x_4504_ = l_Lean_Syntax_matchesNull(v___x_4502_, v___x_4471_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
lean_dec(v___x_4502_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4505_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4506_ = l_Lean_Syntax_getArg(v___x_4502_, v___x_4382_);
lean_dec(v___x_4502_);
v___x_4507_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4506_);
v___x_4508_ = l_Lean_Syntax_isOfKind(v___x_4506_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
lean_dec(v___x_4506_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4509_;
}
else
{
lean_object* v_patType_x3f_4510_; lean_object* v___x_4511_; 
v_patType_x3f_4510_ = l_Lean_Syntax_getArg(v___x_4506_, v___x_4471_);
lean_dec(v___x_4506_);
v___x_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4511_, 0, v_patType_x3f_4510_);
v_patType_x3f_4473_ = v___x_4511_;
v___y_4474_ = v_a_4366_;
v___y_4475_ = v_a_4367_;
v___y_4476_ = v_a_4368_;
v___y_4477_ = v_a_4369_;
v___y_4478_ = v_a_4370_;
v___y_4479_ = v_a_4371_;
v___y_4480_ = v_a_4372_;
goto v___jp_4472_;
}
}
}
else
{
lean_object* v___x_4512_; 
lean_dec(v___x_4502_);
v___x_4512_ = lean_box(0);
v_patType_x3f_4473_ = v___x_4512_;
v___y_4474_ = v_a_4366_;
v___y_4475_ = v_a_4367_;
v___y_4476_ = v_a_4368_;
v___y_4477_ = v_a_4369_;
v___y_4478_ = v_a_4370_;
v___y_4479_ = v_a_4371_;
v___y_4480_ = v_a_4372_;
goto v___jp_4472_;
}
v___jp_4472_:
{
lean_object* v___x_4481_; lean_object* v_rhs_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4481_ = lean_unsigned_to_nat(3u);
v_rhs_4482_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4481_);
v___x_4483_ = lean_unsigned_to_nat(4u);
v___x_4484_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4483_);
lean_dec(v_stx_4363_);
v___x_4485_ = l_Lean_Syntax_isNone(v___x_4484_);
if (v___x_4485_ == 0)
{
uint8_t v___x_4486_; 
lean_inc(v___x_4484_);
v___x_4486_ = l_Lean_Syntax_matchesNull(v___x_4484_, v___x_4481_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_dec(v___x_4484_);
lean_dec(v_rhs_4482_);
lean_dec(v_patType_x3f_4473_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_letOrReassign_4362_);
v___x_4487_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; lean_object* v_otherwise_x3f_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4488_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4489_ = l_Lean_Syntax_getArg(v___x_4484_, v___x_4471_);
v___x_4490_ = l_Lean_Syntax_getArg(v___x_4484_, v___x_4488_);
lean_dec(v___x_4484_);
v___x_4491_ = l_Lean_Syntax_getOptional_x3f(v___x_4490_);
lean_dec(v___x_4490_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4492_; 
v___x_4492_ = lean_box(0);
v___y_4416_ = v___y_4477_;
v___y_4417_ = v_rhs_4482_;
v___y_4418_ = v___y_4480_;
v___y_4419_ = v_patType_x3f_4473_;
v___y_4420_ = v___y_4474_;
v___y_4421_ = v_otherwise_x3f_4489_;
v___y_4422_ = v___y_4478_;
v___y_4423_ = v___y_4479_;
v___y_4424_ = v___y_4476_;
v___y_4425_ = v___y_4475_;
v___y_4426_ = v___x_4492_;
goto v___jp_4415_;
}
else
{
lean_object* v_val_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
v_val_4493_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4491_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_val_4493_);
lean_dec(v___x_4491_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_val_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
v___y_4416_ = v___y_4477_;
v___y_4417_ = v_rhs_4482_;
v___y_4418_ = v___y_4480_;
v___y_4419_ = v_patType_x3f_4473_;
v___y_4420_ = v___y_4474_;
v___y_4421_ = v_otherwise_x3f_4489_;
v___y_4422_ = v___y_4478_;
v___y_4423_ = v___y_4479_;
v___y_4424_ = v___y_4476_;
v___y_4425_ = v___y_4475_;
v___y_4426_ = v___x_4498_;
goto v___jp_4415_;
}
}
}
}
}
else
{
lean_object* v___x_4501_; 
lean_dec(v___x_4484_);
v___x_4501_ = lean_box(0);
v___y_4387_ = v___y_4475_;
v___y_4388_ = v_patType_x3f_4473_;
v___y_4389_ = v___y_4480_;
v___y_4390_ = v___y_4478_;
v___y_4391_ = v___y_4476_;
v___y_4392_ = v___y_4479_;
v___y_4393_ = v___y_4477_;
v___y_4394_ = v_rhs_4482_;
v___y_4395_ = v___x_4501_;
v___y_4396_ = v___y_4474_;
v___y_4397_ = v___x_4501_;
goto v___jp_4386_;
}
}
}
else
{
lean_object* v_pattern_4513_; lean_object* v___x_4514_; lean_object* v_patType_x3f_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___x_4571_; uint8_t v___x_4572_; 
v_pattern_4513_ = l_Lean_Syntax_getArg(v___x_4383_, v___x_4382_);
v___x_4514_ = lean_unsigned_to_nat(1u);
v___x_4571_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4514_);
v___x_4572_ = l_Lean_Syntax_isNone(v___x_4571_);
if (v___x_4572_ == 0)
{
uint8_t v___x_4573_; 
lean_inc(v___x_4571_);
v___x_4573_ = l_Lean_Syntax_matchesNull(v___x_4571_, v___x_4514_);
if (v___x_4573_ == 0)
{
lean_object* v___x_4574_; 
lean_dec(v___x_4571_);
lean_dec(v_pattern_4513_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4575_ = l_Lean_Syntax_getArg(v___x_4571_, v___x_4382_);
lean_dec(v___x_4571_);
v___x_4576_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4575_);
v___x_4577_ = l_Lean_Syntax_isOfKind(v___x_4575_, v___x_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; 
lean_dec(v___x_4575_);
lean_dec(v_pattern_4513_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4578_;
}
else
{
lean_object* v_patType_x3f_4579_; lean_object* v___x_4580_; 
v_patType_x3f_4579_ = l_Lean_Syntax_getArg(v___x_4575_, v___x_4514_);
lean_dec(v___x_4575_);
v___x_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4580_, 0, v_patType_x3f_4579_);
v_patType_x3f_4516_ = v___x_4580_;
v___y_4517_ = v_a_4366_;
v___y_4518_ = v_a_4367_;
v___y_4519_ = v_a_4368_;
v___y_4520_ = v_a_4369_;
v___y_4521_ = v_a_4370_;
v___y_4522_ = v_a_4371_;
v___y_4523_ = v_a_4372_;
goto v___jp_4515_;
}
}
}
else
{
lean_object* v___x_4581_; 
lean_dec(v___x_4571_);
v___x_4581_ = lean_box(0);
v_patType_x3f_4516_ = v___x_4581_;
v___y_4517_ = v_a_4366_;
v___y_4518_ = v_a_4367_;
v___y_4519_ = v_a_4368_;
v___y_4520_ = v_a_4369_;
v___y_4521_ = v_a_4370_;
v___y_4522_ = v_a_4371_;
v___y_4523_ = v_a_4372_;
goto v___jp_4515_;
}
v___jp_4515_:
{
lean_object* v___x_4524_; lean_object* v_rhs_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4524_ = lean_unsigned_to_nat(3u);
v_rhs_4525_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4524_);
v___x_4526_ = lean_unsigned_to_nat(4u);
v___x_4527_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4526_);
lean_dec(v_stx_4363_);
lean_inc(v___x_4527_);
v___x_4528_ = l_Lean_Syntax_matchesNull(v___x_4527_, v___x_4382_);
if (v___x_4528_ == 0)
{
uint8_t v___x_4529_; 
lean_dec(v_pattern_4513_);
v___x_4529_ = l_Lean_Syntax_isNone(v___x_4527_);
if (v___x_4529_ == 0)
{
uint8_t v___x_4530_; 
lean_inc(v___x_4527_);
v___x_4530_ = l_Lean_Syntax_matchesNull(v___x_4527_, v___x_4524_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_dec(v___x_4527_);
lean_dec(v_rhs_4525_);
lean_dec(v_patType_x3f_4516_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_letOrReassign_4362_);
v___x_4531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; lean_object* v_otherwise_x3f_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4532_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4533_ = l_Lean_Syntax_getArg(v___x_4527_, v___x_4514_);
v___x_4534_ = l_Lean_Syntax_getArg(v___x_4527_, v___x_4532_);
lean_dec(v___x_4527_);
v___x_4535_ = l_Lean_Syntax_getOptional_x3f(v___x_4534_);
lean_dec(v___x_4534_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_box(0);
v___y_4459_ = v___y_4522_;
v___y_4460_ = v___y_4521_;
v___y_4461_ = v___y_4520_;
v___y_4462_ = v_otherwise_x3f_4533_;
v___y_4463_ = v_patType_x3f_4516_;
v___y_4464_ = v_rhs_4525_;
v___y_4465_ = v___y_4519_;
v___y_4466_ = v___y_4518_;
v___y_4467_ = v___y_4523_;
v___y_4468_ = v___y_4517_;
v___y_4469_ = v___x_4536_;
goto v___jp_4458_;
}
else
{
lean_object* v_val_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_val_4537_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4535_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_val_4537_);
lean_dec(v___x_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_val_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
v___y_4459_ = v___y_4522_;
v___y_4460_ = v___y_4521_;
v___y_4461_ = v___y_4520_;
v___y_4462_ = v_otherwise_x3f_4533_;
v___y_4463_ = v_patType_x3f_4516_;
v___y_4464_ = v_rhs_4525_;
v___y_4465_ = v___y_4519_;
v___y_4466_ = v___y_4518_;
v___y_4467_ = v___y_4523_;
v___y_4468_ = v___y_4517_;
v___y_4469_ = v___x_4542_;
goto v___jp_4458_;
}
}
}
}
}
else
{
lean_object* v___x_4545_; 
lean_dec(v___x_4527_);
v___x_4545_ = lean_box(0);
v___y_4429_ = v___y_4519_;
v___y_4430_ = v_patType_x3f_4516_;
v___y_4431_ = v___y_4520_;
v___y_4432_ = v___y_4518_;
v___y_4433_ = v___y_4521_;
v___y_4434_ = v___y_4517_;
v___y_4435_ = v___x_4545_;
v___y_4436_ = v___y_4523_;
v___y_4437_ = v_rhs_4525_;
v___y_4438_ = v___y_4522_;
v___y_4439_ = v___x_4545_;
goto v___jp_4428_;
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec(v___x_4527_);
lean_dec(v___x_4383_);
lean_dec(v_letOrReassign_4362_);
v___x_4546_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4547_ = l_Lean_Core_mkFreshUserName(v___x_4546_, v___y_4522_, v___y_4523_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4549_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4547_);
v___x_4549_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4365_, v_tk_4364_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; uint8_t v_kind_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref(v___x_4549_);
v_kind_4551_ = lean_ctor_get_uint8(v_a_4550_, sizeof(void*)*3);
v___x_4552_ = l_Lean_mkIdentFrom(v_pattern_4513_, v_a_4548_, v___x_4378_);
lean_dec(v_pattern_4513_);
v___x_4553_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4553_, 0, v_a_4550_);
v___x_4554_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4552_, v_patType_x3f_4516_, v_rhs_4525_, v___x_4553_, v_kind_4551_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4548_);
lean_dec(v_rhs_4525_);
lean_dec(v_patType_x3f_4516_);
lean_dec(v_pattern_4513_);
v_a_4555_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4549_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4549_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_rhs_4525_);
lean_dec(v_patType_x3f_4516_);
lean_dec(v_pattern_4513_);
lean_dec_ref(v_dec_4365_);
v_a_4563_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4547_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4547_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
}
v___jp_4386_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4399_ = l_Lean_Core_mkFreshUserName(v___x_4398_, v___y_4392_, v___y_4389_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___y_4404_; uint8_t v___x_4405_; lean_object* v___x_4406_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref(v___x_4399_);
v___x_4401_ = l_Lean_mkIdentFrom(v___x_4383_, v_a_4400_, v___x_4385_);
v___x_4402_ = lean_box(v___x_4385_);
v___x_4403_ = lean_box(v___x_4380_);
lean_inc(v___x_4401_);
v___y_4404_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4404_, 0, v_letOrReassign_4362_);
lean_closure_set(v___y_4404_, 1, v___y_4395_);
lean_closure_set(v___y_4404_, 2, v___x_4402_);
lean_closure_set(v___y_4404_, 3, v___x_4374_);
lean_closure_set(v___y_4404_, 4, v___x_4375_);
lean_closure_set(v___y_4404_, 5, v___x_4376_);
lean_closure_set(v___y_4404_, 6, v___x_4383_);
lean_closure_set(v___y_4404_, 7, v___x_4401_);
lean_closure_set(v___y_4404_, 8, v_dec_4365_);
lean_closure_set(v___y_4404_, 9, v___x_4403_);
lean_closure_set(v___y_4404_, 10, v___y_4397_);
lean_closure_set(v___y_4404_, 11, v___x_4382_);
v___x_4405_ = 0;
v___x_4406_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4401_, v___y_4388_, v___y_4394_, v___y_4404_, v___x_4405_, v___y_4396_, v___y_4387_, v___y_4391_, v___y_4393_, v___y_4390_, v___y_4392_, v___y_4389_);
return v___x_4406_;
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v___y_4397_);
lean_dec(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec(v___y_4388_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_letOrReassign_4362_);
v_a_4407_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4399_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4399_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
v___jp_4415_:
{
lean_object* v___x_4427_; 
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___y_4421_);
v___y_4387_ = v___y_4425_;
v___y_4388_ = v___y_4419_;
v___y_4389_ = v___y_4418_;
v___y_4390_ = v___y_4422_;
v___y_4391_ = v___y_4424_;
v___y_4392_ = v___y_4423_;
v___y_4393_ = v___y_4416_;
v___y_4394_ = v___y_4417_;
v___y_4395_ = v___x_4427_;
v___y_4396_ = v___y_4420_;
v___y_4397_ = v___y_4426_;
goto v___jp_4386_;
}
v___jp_4428_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4441_ = l_Lean_Core_mkFreshUserName(v___x_4440_, v___y_4438_, v___y_4436_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___y_4447_; uint8_t v___x_4448_; lean_object* v___x_4449_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_a_4442_);
lean_dec_ref(v___x_4441_);
v___x_4443_ = l_Lean_mkIdentFrom(v___x_4383_, v_a_4442_, v___x_4378_);
v___x_4444_ = lean_box(v___x_4378_);
v___x_4445_ = lean_box(v___x_4380_);
v___x_4446_ = lean_box(v___x_4385_);
lean_inc(v___x_4443_);
v___y_4447_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4447_, 0, v_letOrReassign_4362_);
lean_closure_set(v___y_4447_, 1, v___y_4435_);
lean_closure_set(v___y_4447_, 2, v___x_4444_);
lean_closure_set(v___y_4447_, 3, v___x_4374_);
lean_closure_set(v___y_4447_, 4, v___x_4375_);
lean_closure_set(v___y_4447_, 5, v___x_4376_);
lean_closure_set(v___y_4447_, 6, v___x_4383_);
lean_closure_set(v___y_4447_, 7, v___x_4443_);
lean_closure_set(v___y_4447_, 8, v_dec_4365_);
lean_closure_set(v___y_4447_, 9, v___x_4445_);
lean_closure_set(v___y_4447_, 10, v___y_4439_);
lean_closure_set(v___y_4447_, 11, v___x_4382_);
lean_closure_set(v___y_4447_, 12, v___x_4446_);
v___x_4448_ = 0;
v___x_4449_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4443_, v___y_4430_, v___y_4437_, v___y_4447_, v___x_4448_, v___y_4434_, v___y_4432_, v___y_4429_, v___y_4431_, v___y_4433_, v___y_4438_, v___y_4436_);
return v___x_4449_;
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v___y_4439_);
lean_dec(v___y_4437_);
lean_dec(v___y_4435_);
lean_dec(v___y_4430_);
lean_dec(v___x_4383_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_letOrReassign_4362_);
v_a_4450_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4441_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4441_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
v___jp_4458_:
{
lean_object* v___x_4470_; 
v___x_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___y_4462_);
v___y_4429_ = v___y_4465_;
v___y_4430_ = v___y_4463_;
v___y_4431_ = v___y_4461_;
v___y_4432_ = v___y_4466_;
v___y_4433_ = v___y_4460_;
v___y_4434_ = v___y_4468_;
v___y_4435_ = v___x_4470_;
v___y_4436_ = v___y_4467_;
v___y_4437_ = v___y_4464_;
v___y_4438_ = v___y_4459_;
v___y_4439_ = v___y_4469_;
goto v___jp_4428_;
}
}
}
else
{
lean_object* v___x_4582_; lean_object* v_x_4583_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v_xType_x3f_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v_xType_x3f_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4582_ = lean_unsigned_to_nat(0u);
v_x_4583_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4582_);
v___x_4656_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4583_);
v___x_4657_ = l_Lean_Syntax_isOfKind(v_x_4583_, v___x_4656_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; 
lean_dec(v_x_4583_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4658_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4658_;
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4659_ = lean_unsigned_to_nat(1u);
v___x_4660_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4659_);
v___x_4661_ = l_Lean_Syntax_isNone(v___x_4660_);
if (v___x_4661_ == 0)
{
uint8_t v___x_4662_; 
lean_inc(v___x_4660_);
v___x_4662_ = l_Lean_Syntax_matchesNull(v___x_4660_, v___x_4659_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; 
lean_dec(v___x_4660_);
lean_dec(v_x_4583_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4663_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4663_;
}
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4664_ = l_Lean_Syntax_getArg(v___x_4660_, v___x_4582_);
lean_dec(v___x_4660_);
v___x_4665_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4664_);
v___x_4666_ = l_Lean_Syntax_isOfKind(v___x_4664_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; 
lean_dec(v___x_4664_);
lean_dec(v_x_4583_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v___x_4667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4667_;
}
else
{
lean_object* v_xType_x3f_4668_; lean_object* v___x_4669_; 
v_xType_x3f_4668_ = l_Lean_Syntax_getArg(v___x_4664_, v___x_4659_);
lean_dec(v___x_4664_);
v___x_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4669_, 0, v_xType_x3f_4668_);
v_xType_x3f_4601_ = v___x_4669_;
v___y_4602_ = v_a_4366_;
v___y_4603_ = v_a_4367_;
v___y_4604_ = v_a_4368_;
v___y_4605_ = v_a_4369_;
v___y_4606_ = v_a_4370_;
v___y_4607_ = v_a_4371_;
v___y_4608_ = v_a_4372_;
goto v___jp_4600_;
}
}
}
else
{
lean_object* v___x_4670_; 
lean_dec(v___x_4660_);
v___x_4670_ = lean_box(0);
v_xType_x3f_4601_ = v___x_4670_;
v___y_4602_ = v_a_4366_;
v___y_4603_ = v_a_4367_;
v___y_4604_ = v_a_4368_;
v___y_4605_ = v_a_4369_;
v___y_4606_ = v_a_4370_;
v___y_4607_ = v_a_4371_;
v___y_4608_ = v_a_4372_;
goto v___jp_4600_;
}
}
v___jp_4584_:
{
uint8_t v_kind_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v_kind_4595_ = lean_ctor_get_uint8(v___y_4585_, sizeof(void*)*3);
v___x_4596_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4362_);
lean_dec(v_letOrReassign_4362_);
v___x_4597_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4597_, 0, v___y_4585_);
lean_inc(v_x_4583_);
v___x_4598_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4598_, 0, lean_box(0));
lean_closure_set(v___x_4598_, 1, v___x_4596_);
lean_closure_set(v___x_4598_, 2, v_x_4583_);
lean_closure_set(v___x_4598_, 3, v___x_4597_);
v___x_4599_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4583_, v_xType_x3f_4587_, v___y_4586_, v___x_4598_, v_kind_4595_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4599_;
}
v___jp_4600_:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4609_ = lean_unsigned_to_nat(1u);
v___x_4610_ = lean_mk_empty_array_with_capacity(v___x_4609_);
lean_inc(v_x_4583_);
v___x_4611_ = lean_array_push(v___x_4610_, v_x_4583_);
v___x_4612_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4362_, v___x_4611_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec_ref(v___x_4611_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v___x_4613_; 
lean_dec_ref(v___x_4612_);
v___x_4613_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4365_, v_tk_4364_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4615_; lean_object* v_rhs_4616_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4614_);
lean_dec_ref(v___x_4613_);
v___x_4615_ = lean_unsigned_to_nat(3u);
v_rhs_4616_ = l_Lean_Syntax_getArg(v_stx_4363_, v___x_4615_);
lean_dec(v_stx_4363_);
if (lean_obj_tag(v_letOrReassign_4362_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4601_) == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = l_Lean_TSyntax_getId(v_x_4583_);
v___x_4618_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4617_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_a_4619_);
lean_dec_ref(v___x_4618_);
v___x_4620_ = l_Lean_LocalDecl_type(v_a_4619_);
lean_dec(v_a_4619_);
v___x_4621_ = l_Lean_Elab_Term_exprToSyntax(v___x_4620_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref(v___x_4621_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_a_4622_);
v___y_4585_ = v_a_4614_;
v___y_4586_ = v_rhs_4616_;
v_xType_x3f_4587_ = v___x_4623_;
v___y_4588_ = v___y_4602_;
v___y_4589_ = v___y_4603_;
v___y_4590_ = v___y_4604_;
v___y_4591_ = v___y_4605_;
v___y_4592_ = v___y_4606_;
v___y_4593_ = v___y_4607_;
v___y_4594_ = v___y_4608_;
goto v___jp_4584_;
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_rhs_4616_);
lean_dec(v_a_4614_);
lean_dec(v_x_4583_);
v_a_4624_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4621_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4621_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec(v_rhs_4616_);
lean_dec(v_a_4614_);
lean_dec(v_x_4583_);
v_a_4632_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4618_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4618_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
else
{
v___y_4585_ = v_a_4614_;
v___y_4586_ = v_rhs_4616_;
v_xType_x3f_4587_ = v_xType_x3f_4601_;
v___y_4588_ = v___y_4602_;
v___y_4589_ = v___y_4603_;
v___y_4590_ = v___y_4604_;
v___y_4591_ = v___y_4605_;
v___y_4592_ = v___y_4606_;
v___y_4593_ = v___y_4607_;
v___y_4594_ = v___y_4608_;
goto v___jp_4584_;
}
}
else
{
v___y_4585_ = v_a_4614_;
v___y_4586_ = v_rhs_4616_;
v_xType_x3f_4587_ = v_xType_x3f_4601_;
v___y_4588_ = v___y_4602_;
v___y_4589_ = v___y_4603_;
v___y_4590_ = v___y_4604_;
v___y_4591_ = v___y_4605_;
v___y_4592_ = v___y_4606_;
v___y_4593_ = v___y_4607_;
v___y_4594_ = v___y_4608_;
goto v___jp_4584_;
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v_xType_x3f_4601_);
lean_dec(v_x_4583_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v_a_4640_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4613_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4613_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec(v_xType_x3f_4601_);
lean_dec(v_x_4583_);
lean_dec_ref(v_dec_4365_);
lean_dec(v_stx_4363_);
lean_dec(v_letOrReassign_4362_);
v_a_4648_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4612_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4612_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4671_, lean_object* v_stx_4672_, lean_object* v_tk_4673_, lean_object* v_dec_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4671_, v_stx_4672_, v_tk_4673_, v_dec_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec_ref(v_a_4675_);
lean_dec(v_tk_4673_);
return v_res_4683_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4686_ = l_Lean_stringToMessageData(v___x_4685_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4687_, lean_object* v_mutTk_x3f_4688_, lean_object* v_initConfig_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4688_) == 0)
{
lean_object* v___x_4697_; 
v___x_4697_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4687_, v_initConfig_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
return v___x_4697_;
}
else
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = l_Lean_Syntax_getArg(v_letConfigStx_4687_, v___x_4698_);
v___x_4700_ = l_Lean_Syntax_getArgs(v___x_4699_);
lean_dec(v___x_4699_);
v___x_4701_ = lean_array_get_size(v___x_4700_);
lean_dec_ref(v___x_4700_);
v___x_4702_ = lean_nat_dec_eq(v___x_4701_, v___x_4698_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v_initConfig_4689_);
v___x_4703_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4704_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4687_, v___x_4703_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_letConfigStx_4687_);
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
else
{
lean_object* v___x_4713_; 
v___x_4713_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4687_, v_initConfig_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
return v___x_4713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4714_, lean_object* v_mutTk_x3f_4715_, lean_object* v_initConfig_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4714_, v_mutTk_x3f_4715_, v_initConfig_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
lean_dec(v_mutTk_x3f_4715_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4725_, lean_object* v_mutTk_x3f_4726_, lean_object* v_initConfig_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4725_, v_mutTk_x3f_4726_, v_initConfig_4727_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4737_, lean_object* v_mutTk_x3f_4738_, lean_object* v_initConfig_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4737_, v_mutTk_x3f_4738_, v_initConfig_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec(v_a_4746_);
lean_dec_ref(v_a_4745_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
lean_dec_ref(v_a_4740_);
lean_dec(v_mutTk_x3f_4738_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4762_, lean_object* v_dec_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v___x_4772_; uint8_t v___x_4773_; 
v___x_4772_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4762_);
v___x_4773_ = l_Lean_Syntax_isOfKind(v_stx_4762_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v___x_4774_; 
lean_dec_ref(v_dec_4763_);
lean_dec(v_stx_4762_);
v___x_4774_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4774_;
}
else
{
lean_object* v___x_4775_; lean_object* v_tk_4776_; lean_object* v_mutTk_x3f_4778_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4775_ = lean_unsigned_to_nat(0u);
v_tk_4776_ = l_Lean_Syntax_getArg(v_stx_4762_, v___x_4775_);
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = l_Lean_Syntax_getArg(v_stx_4762_, v___x_4809_);
v___x_4811_ = l_Lean_Syntax_isNone(v___x_4810_);
if (v___x_4811_ == 0)
{
uint8_t v___x_4812_; 
lean_inc(v___x_4810_);
v___x_4812_ = l_Lean_Syntax_matchesNull(v___x_4810_, v___x_4809_);
if (v___x_4812_ == 0)
{
lean_object* v___x_4813_; 
lean_dec(v___x_4810_);
lean_dec(v_tk_4776_);
lean_dec_ref(v_dec_4763_);
lean_dec(v_stx_4762_);
v___x_4813_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4813_;
}
else
{
lean_object* v_mutTk_x3f_4814_; lean_object* v___x_4815_; 
v_mutTk_x3f_4814_ = l_Lean_Syntax_getArg(v___x_4810_, v___x_4775_);
lean_dec(v___x_4810_);
v___x_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4815_, 0, v_mutTk_x3f_4814_);
v_mutTk_x3f_4778_ = v___x_4815_;
v___y_4779_ = v_a_4764_;
v___y_4780_ = v_a_4765_;
v___y_4781_ = v_a_4766_;
v___y_4782_ = v_a_4767_;
v___y_4783_ = v_a_4768_;
v___y_4784_ = v_a_4769_;
v___y_4785_ = v_a_4770_;
goto v___jp_4777_;
}
}
else
{
lean_object* v___x_4816_; 
lean_dec(v___x_4810_);
v___x_4816_ = lean_box(0);
v_mutTk_x3f_4778_ = v___x_4816_;
v___y_4779_ = v_a_4764_;
v___y_4780_ = v_a_4765_;
v___y_4781_ = v_a_4766_;
v___y_4782_ = v_a_4767_;
v___y_4783_ = v_a_4768_;
v___y_4784_ = v_a_4769_;
v___y_4785_ = v_a_4770_;
goto v___jp_4777_;
}
v___jp_4777_:
{
lean_object* v___x_4786_; lean_object* v_config_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4786_ = lean_unsigned_to_nat(2u);
v_config_4787_ = l_Lean_Syntax_getArg(v_stx_4762_, v___x_4786_);
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4787_);
v___x_4789_ = l_Lean_Syntax_isOfKind(v_config_4787_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec(v_config_4787_);
lean_dec(v_mutTk_x3f_4778_);
lean_dec(v_tk_4776_);
lean_dec_ref(v_dec_4763_);
lean_dec(v_stx_4762_);
v___x_4790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4790_;
}
else
{
lean_object* v___x_4791_; lean_object* v_decl_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4791_ = lean_unsigned_to_nat(3u);
v_decl_4792_ = l_Lean_Syntax_getArg(v_stx_4762_, v___x_4791_);
lean_dec(v_stx_4762_);
v___x_4793_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4792_);
v___x_4794_ = l_Lean_Syntax_isOfKind(v_decl_4792_, v___x_4793_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; 
lean_dec(v_decl_4792_);
lean_dec(v_config_4787_);
lean_dec(v_mutTk_x3f_4778_);
lean_dec(v_tk_4776_);
lean_dec_ref(v_dec_4763_);
v___x_4795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4795_;
}
else
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4797_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4787_, v_mutTk_x3f_4778_, v___x_4796_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref(v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v_mutTk_x3f_4778_);
v___x_4800_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4798_, v___x_4799_, v_decl_4792_, v_tk_4776_, v_dec_4763_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
return v___x_4800_;
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_decl_4792_);
lean_dec(v_mutTk_x3f_4778_);
lean_dec(v_tk_4776_);
lean_dec_ref(v_dec_4763_);
v_a_4801_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4797_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4797_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4817_, lean_object* v_dec_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_Elab_Do_elabDoLet(v_stx_4817_, v_dec_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec_ref(v_a_4819_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4835_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4836_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4837_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4838_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4839_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4835_, v___x_4836_, v___x_4837_, v___x_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4847_, lean_object* v_dec_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4857_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4847_);
v___x_4858_ = l_Lean_Syntax_isOfKind(v_stx_4847_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; 
lean_dec_ref(v_dec_4848_);
lean_dec(v_stx_4847_);
v___x_4859_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4859_;
}
else
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4860_ = lean_unsigned_to_nat(1u);
v___x_4861_ = l_Lean_Syntax_getArg(v_stx_4847_, v___x_4860_);
v___x_4862_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4861_);
v___x_4863_ = l_Lean_Syntax_isOfKind(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; 
lean_dec(v___x_4861_);
lean_dec_ref(v_dec_4848_);
lean_dec(v_stx_4847_);
v___x_4864_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4864_;
}
else
{
lean_object* v___x_4865_; lean_object* v_decl_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4865_ = lean_unsigned_to_nat(2u);
v_decl_4866_ = l_Lean_Syntax_getArg(v_stx_4847_, v___x_4865_);
v___x_4867_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4866_);
v___x_4868_ = l_Lean_Syntax_isOfKind(v_decl_4866_, v___x_4867_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; 
lean_dec(v_decl_4866_);
lean_dec(v___x_4861_);
lean_dec_ref(v_dec_4848_);
lean_dec(v_stx_4847_);
v___x_4869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4869_;
}
else
{
uint8_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4870_ = 0;
v___x_4871_ = lean_box(0);
v___x_4872_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*1, v___x_4868_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*1 + 1, v___x_4870_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*1 + 2, v___x_4870_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*1 + 3, v___x_4870_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*1 + 4, v___x_4870_);
v___x_4873_ = l_Lean_Elab_Term_mkLetConfig(v___x_4861_, v___x_4872_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; lean_object* v_tk_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref(v___x_4873_);
v___x_4875_ = lean_unsigned_to_nat(0u);
v_tk_4876_ = l_Lean_Syntax_getArg(v_stx_4847_, v___x_4875_);
lean_dec(v_stx_4847_);
v___x_4877_ = lean_box(1);
v___x_4878_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4874_, v___x_4877_, v_decl_4866_, v_tk_4876_, v_dec_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4878_;
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec(v_decl_4866_);
lean_dec_ref(v_dec_4848_);
lean_dec(v_stx_4847_);
v_a_4879_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4873_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4873_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4887_, lean_object* v_dec_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_Elab_Do_elabDoHave(v_stx_4887_, v_dec_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec_ref(v_a_4889_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4905_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4906_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4908_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4909_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4905_, v___x_4906_, v___x_4907_, v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4914_, lean_object* v___x_4915_, lean_object* v___x_4916_, lean_object* v___x_4917_, lean_object* v_decls_4918_, lean_object* v_a_4919_, uint8_t v___x_4920_, lean_object* v_body_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_ref_4930_; uint8_t v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v_ref_4930_ = lean_ctor_get(v___y_4927_, 5);
v___x_4931_ = 0;
v___x_4932_ = l_Lean_SourceInfo_fromRef(v_ref_4930_, v___x_4931_);
v___x_4933_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4934_ = l_Lean_Name_mkStr4(v___x_4914_, v___x_4915_, v___x_4916_, v___x_4933_);
v___x_4935_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4932_, 4);
v___x_4936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4932_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4932_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = l_Lean_Syntax_node2(v___x_4932_, v___x_4917_, v___x_4936_, v___x_4938_);
v___x_4940_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4932_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l_Lean_Syntax_node4(v___x_4932_, v___x_4934_, v___x_4939_, v_decls_4918_, v___x_4941_, v_body_4921_);
v___x_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_a_4919_);
v___x_4944_ = l_Lean_Elab_Term_elabTerm(v___x_4942_, v___x_4943_, v___x_4920_, v___x_4920_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4945_, lean_object* v___x_4946_, lean_object* v___x_4947_, lean_object* v___x_4948_, lean_object* v_decls_4949_, lean_object* v_a_4950_, lean_object* v___x_4951_, lean_object* v_body_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
uint8_t v___x_5027__boxed_4961_; lean_object* v_res_4962_; 
v___x_5027__boxed_4961_ = lean_unbox(v___x_4951_);
v_res_4962_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4945_, v___x_4946_, v___x_4947_, v___x_4948_, v_decls_4949_, v_a_4950_, v___x_5027__boxed_4961_, v_body_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v___y_4953_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
if (lean_obj_tag(v_a_4963_) == 0)
{
lean_object* v___x_4965_; 
v___x_4965_ = l_List_reverse___redArg(v_a_4964_);
return v___x_4965_;
}
else
{
lean_object* v_head_4966_; lean_object* v_tail_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4976_; 
v_head_4966_ = lean_ctor_get(v_a_4963_, 0);
v_tail_4967_ = lean_ctor_get(v_a_4963_, 1);
v_isSharedCheck_4976_ = !lean_is_exclusive(v_a_4963_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4969_ = v_a_4963_;
v_isShared_4970_ = v_isSharedCheck_4976_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_tail_4967_);
lean_inc(v_head_4966_);
lean_dec(v_a_4963_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4976_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = l_Lean_MessageData_ofSyntax(v_head_4966_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 1, v_a_4964_);
lean_ctor_set(v___x_4969_, 0, v___x_4971_);
v___x_4973_ = v___x_4969_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_a_4964_);
v___x_4973_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
v_a_4963_ = v_tail_4967_;
v_a_4964_ = v___x_4973_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4994_ = l_Lean_stringToMessageData(v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4995_, lean_object* v_dec_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5005_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5006_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5007_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5008_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4995_);
v___x_5009_ = l_Lean_Syntax_isOfKind(v_stx_4995_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_dec_ref(v_dec_4996_);
lean_dec(v_stx_4995_);
v___x_5010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; uint8_t v___x_5014_; 
v___x_5011_ = lean_unsigned_to_nat(0u);
v___x_5012_ = l_Lean_Syntax_getArg(v_stx_4995_, v___x_5011_);
v___x_5013_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5012_);
v___x_5014_ = l_Lean_Syntax_isOfKind(v___x_5012_, v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; 
lean_dec(v___x_5012_);
lean_dec_ref(v_dec_4996_);
lean_dec(v_stx_4995_);
v___x_5015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5015_;
}
else
{
lean_object* v___x_5016_; lean_object* v_decls_5017_; lean_object* v___x_5018_; uint8_t v___x_5019_; 
v___x_5016_ = lean_unsigned_to_nat(1u);
v_decls_5017_ = l_Lean_Syntax_getArg(v_stx_4995_, v___x_5016_);
lean_dec(v_stx_4995_);
v___x_5018_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5017_);
v___x_5019_ = l_Lean_Syntax_isOfKind(v_decls_5017_, v___x_5018_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
lean_dec(v_decls_5017_);
lean_dec(v___x_5012_);
lean_dec_ref(v_dec_4996_);
v___x_5020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5020_;
}
else
{
lean_object* v_tk_5021_; lean_object* v___x_5022_; 
v_tk_5021_ = l_Lean_Syntax_getArg(v___x_5012_, v___x_5011_);
lean_dec(v___x_5012_);
v___x_5022_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4996_, v_tk_5021_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
lean_dec(v_tk_5021_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5024_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref(v___x_5022_);
lean_inc(v_decls_5017_);
v___x_5024_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5017_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v_doBlockResultType_5026_; lean_object* v___x_5027_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref(v___x_5024_);
v_doBlockResultType_5026_ = lean_ctor_get(v_a_4997_, 3);
lean_inc_ref(v_doBlockResultType_5026_);
v___x_5027_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_5026_, v_a_4997_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; lean_object* v___f_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref(v___x_5027_);
v___x_5029_ = lean_box(v___x_5019_);
v___f_5030_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5030_, 0, v___x_5005_);
lean_closure_set(v___f_5030_, 1, v___x_5006_);
lean_closure_set(v___f_5030_, 2, v___x_5007_);
lean_closure_set(v___f_5030_, 3, v___x_5013_);
lean_closure_set(v___f_5030_, 4, v_decls_5017_);
lean_closure_set(v___f_5030_, 5, v_a_5028_);
lean_closure_set(v___f_5030_, 6, v___x_5029_);
v___x_5031_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5032_ = lean_array_to_list(v_a_5025_);
v___x_5033_ = lean_box(0);
v___x_5034_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5032_, v___x_5033_);
v___x_5035_ = l_Lean_MessageData_ofList(v___x_5034_);
v___x_5036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5031_);
lean_ctor_set(v___x_5036_, 1, v___x_5035_);
v___x_5037_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5037_, 0, v_a_5023_);
v___x_5038_ = lean_box(0);
v___x_5039_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5036_, v___x_5037_, v___f_5030_, v___x_5038_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
return v___x_5039_;
}
else
{
lean_dec(v_a_5025_);
lean_dec(v_a_5023_);
lean_dec(v_decls_5017_);
return v___x_5027_;
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_a_5023_);
lean_dec(v_decls_5017_);
v_a_5040_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_5024_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5024_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec(v_decls_5017_);
v_a_5048_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5022_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5022_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5056_, lean_object* v_dec_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5056_, v_dec_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec_ref(v_a_5058_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5074_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5075_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5076_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5077_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5078_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5074_, v___x_5075_, v___x_5076_, v___x_5077_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5094_, lean_object* v_dec_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; uint8_t v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___x_5137_; uint8_t v___x_5138_; 
v___x_5137_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_5094_);
v___x_5138_ = l_Lean_Syntax_isOfKind(v_stx_5094_, v___x_5137_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; 
lean_dec_ref(v_dec_5095_);
lean_dec(v_stx_5094_);
v___x_5139_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5139_;
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; uint8_t v___x_5143_; 
v___x_5140_ = lean_unsigned_to_nat(0u);
v___x_5141_ = l_Lean_Syntax_getArg(v_stx_5094_, v___x_5140_);
lean_dec(v_stx_5094_);
v___x_5142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5141_);
v___x_5143_ = l_Lean_Syntax_isOfKind(v___x_5141_, v___x_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5141_);
v___x_5145_ = l_Lean_Syntax_isOfKind(v___x_5141_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5146_;
}
else
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v_decl_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5147_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = lean_mk_empty_array_with_capacity(v___x_5148_);
v___x_5150_ = lean_array_push(v___x_5149_, v___x_5141_);
v___x_5151_ = lean_box(2);
v_decl_5152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5152_, 0, v___x_5151_);
lean_ctor_set(v_decl_5152_, 1, v___x_5147_);
lean_ctor_set(v_decl_5152_, 2, v___x_5150_);
v___x_5153_ = lean_box(0);
v___x_5154_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5154_, 0, v___x_5153_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1, v___x_5143_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1 + 1, v___x_5143_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1 + 2, v___x_5143_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1 + 3, v___x_5143_);
lean_ctor_set_uint8(v___x_5154_, sizeof(void*)*1 + 4, v___x_5143_);
v___x_5155_ = lean_box(2);
lean_inc_ref(v_decl_5152_);
v___x_5156_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5154_, v___x_5155_, v_decl_5152_, v_decl_5152_, v_dec_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
return v___x_5156_;
}
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5157_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5140_);
v___x_5158_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5157_);
v___x_5159_ = l_Lean_Syntax_isOfKind(v___x_5157_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_object* v___x_5160_; 
lean_dec(v___x_5157_);
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5160_;
}
else
{
lean_object* v___x_5161_; lean_object* v_xType_x3f_5163_; lean_object* v___y_5164_; lean_object* v___y_5165_; lean_object* v___y_5166_; lean_object* v___y_5167_; lean_object* v___y_5168_; lean_object* v___y_5169_; lean_object* v___y_5170_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5161_ = l_Lean_Syntax_getArg(v___x_5157_, v___x_5140_);
lean_dec(v___x_5157_);
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5161_);
v___x_5191_ = l_Lean_Syntax_isOfKind(v___x_5161_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_object* v___x_5192_; 
lean_dec(v___x_5161_);
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5192_;
}
else
{
lean_object* v___x_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; 
v___x_5193_ = lean_unsigned_to_nat(1u);
v___x_5194_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5193_);
v___x_5195_ = l_Lean_Syntax_matchesNull(v___x_5194_, v___x_5140_);
if (v___x_5195_ == 0)
{
lean_object* v___x_5196_; 
lean_dec(v___x_5161_);
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5196_;
}
else
{
lean_object* v___x_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; 
v___x_5197_ = lean_unsigned_to_nat(2u);
v___x_5198_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5197_);
v___x_5199_ = l_Lean_Syntax_isNone(v___x_5198_);
if (v___x_5199_ == 0)
{
uint8_t v___x_5200_; 
lean_inc(v___x_5198_);
v___x_5200_ = l_Lean_Syntax_matchesNull(v___x_5198_, v___x_5193_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
lean_dec(v___x_5198_);
lean_dec(v___x_5161_);
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; 
v___x_5202_ = l_Lean_Syntax_getArg(v___x_5198_, v___x_5140_);
lean_dec(v___x_5198_);
v___x_5203_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5202_);
v___x_5204_ = l_Lean_Syntax_isOfKind(v___x_5202_, v___x_5203_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5205_; 
lean_dec(v___x_5202_);
lean_dec(v___x_5161_);
lean_dec(v___x_5141_);
lean_dec_ref(v_dec_5095_);
v___x_5205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5205_;
}
else
{
lean_object* v_xType_x3f_5206_; lean_object* v___x_5207_; 
v_xType_x3f_5206_ = l_Lean_Syntax_getArg(v___x_5202_, v___x_5193_);
lean_dec(v___x_5202_);
v___x_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5207_, 0, v_xType_x3f_5206_);
v_xType_x3f_5163_ = v___x_5207_;
v___y_5164_ = v_a_5096_;
v___y_5165_ = v_a_5097_;
v___y_5166_ = v_a_5098_;
v___y_5167_ = v_a_5099_;
v___y_5168_ = v_a_5100_;
v___y_5169_ = v_a_5101_;
v___y_5170_ = v_a_5102_;
goto v___jp_5162_;
}
}
}
else
{
lean_object* v___x_5208_; 
lean_dec(v___x_5198_);
v___x_5208_ = lean_box(0);
v_xType_x3f_5163_ = v___x_5208_;
v___y_5164_ = v_a_5096_;
v___y_5165_ = v_a_5097_;
v___y_5166_ = v_a_5098_;
v___y_5167_ = v_a_5099_;
v___y_5168_ = v_a_5100_;
v___y_5169_ = v_a_5101_;
v___y_5170_ = v_a_5102_;
goto v___jp_5162_;
}
}
}
v___jp_5162_:
{
lean_object* v_ref_5171_; lean_object* v___x_5172_; lean_object* v_tk_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; uint8_t v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v_ref_5171_ = lean_ctor_get(v___y_5169_, 5);
v___x_5172_ = lean_unsigned_to_nat(3u);
v_tk_5173_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5172_);
v___x_5174_ = lean_unsigned_to_nat(4u);
v___x_5175_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5174_);
lean_dec(v___x_5141_);
v___x_5176_ = 0;
v___x_5177_ = l_Lean_SourceInfo_fromRef(v_ref_5171_, v___x_5176_);
v___x_5178_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5177_, 2);
v___x_5179_ = l_Lean_Syntax_node1(v___x_5177_, v___x_5158_, v___x_5161_);
v___x_5180_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5181_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5177_);
lean_ctor_set(v___x_5182_, 1, v___x_5180_);
lean_ctor_set(v___x_5182_, 2, v___x_5181_);
if (lean_obj_tag(v_xType_x3f_5163_) == 1)
{
lean_object* v_val_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v_val_5183_ = lean_ctor_get(v_xType_x3f_5163_, 0);
lean_inc(v_val_5183_);
lean_dec_ref(v_xType_x3f_5163_);
v___x_5184_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5185_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5177_, 2);
v___x_5186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5177_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = l_Lean_Syntax_node2(v___x_5177_, v___x_5184_, v___x_5186_, v_val_5183_);
v___x_5188_ = l_Array_mkArray1___redArg(v___x_5187_);
v___y_5105_ = v___y_5165_;
v___y_5106_ = v___x_5178_;
v___y_5107_ = v___x_5180_;
v___y_5108_ = v___y_5167_;
v___y_5109_ = v___x_5181_;
v___y_5110_ = v___y_5168_;
v___y_5111_ = v___x_5179_;
v___y_5112_ = v___y_5169_;
v___y_5113_ = v___x_5182_;
v___y_5114_ = v_tk_5173_;
v___y_5115_ = v___y_5170_;
v___y_5116_ = v___x_5177_;
v___y_5117_ = v___y_5166_;
v___y_5118_ = v___x_5176_;
v___y_5119_ = v___x_5175_;
v___y_5120_ = v___y_5164_;
v___y_5121_ = v___x_5188_;
goto v___jp_5104_;
}
else
{
lean_object* v___x_5189_; 
lean_dec(v_xType_x3f_5163_);
v___x_5189_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_5105_ = v___y_5165_;
v___y_5106_ = v___x_5178_;
v___y_5107_ = v___x_5180_;
v___y_5108_ = v___y_5167_;
v___y_5109_ = v___x_5181_;
v___y_5110_ = v___y_5168_;
v___y_5111_ = v___x_5179_;
v___y_5112_ = v___y_5169_;
v___y_5113_ = v___x_5182_;
v___y_5114_ = v_tk_5173_;
v___y_5115_ = v___y_5170_;
v___y_5116_ = v___x_5177_;
v___y_5117_ = v___y_5166_;
v___y_5118_ = v___x_5176_;
v___y_5119_ = v___x_5175_;
v___y_5120_ = v___y_5164_;
v___y_5121_ = v___x_5189_;
goto v___jp_5104_;
}
}
}
}
}
v___jp_5104_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
lean_inc_ref(v___y_5109_);
v___x_5122_ = l_Array_append___redArg(v___y_5109_, v___y_5121_);
lean_dec_ref(v___y_5121_);
lean_inc(v___y_5107_);
lean_inc_n(v___y_5116_, 2);
v___x_5123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5123_, 0, v___y_5116_);
lean_ctor_set(v___x_5123_, 1, v___y_5107_);
lean_ctor_set(v___x_5123_, 2, v___x_5122_);
v___x_5124_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5125_, 0, v___y_5116_);
lean_ctor_set(v___x_5125_, 1, v___x_5124_);
lean_inc(v___y_5106_);
v___x_5126_ = l_Lean_Syntax_node5(v___y_5116_, v___y_5106_, v___y_5111_, v___y_5113_, v___x_5123_, v___x_5125_, v___y_5119_);
v___x_5127_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5128_ = lean_unsigned_to_nat(1u);
v___x_5129_ = lean_mk_empty_array_with_capacity(v___x_5128_);
v___x_5130_ = lean_array_push(v___x_5129_, v___x_5126_);
v___x_5131_ = lean_box(2);
v___x_5132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5131_);
lean_ctor_set(v___x_5132_, 1, v___x_5127_);
lean_ctor_set(v___x_5132_, 2, v___x_5130_);
v___x_5133_ = lean_box(0);
v___x_5134_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5134_, 0, v___x_5133_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1, v___y_5118_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1 + 1, v___y_5118_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1 + 2, v___y_5118_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1 + 3, v___y_5118_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1 + 4, v___y_5118_);
v___x_5135_ = lean_box(2);
v___x_5136_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5134_, v___x_5135_, v___x_5132_, v___y_5114_, v_dec_5095_, v___y_5120_, v___y_5105_, v___y_5117_, v___y_5108_, v___y_5110_, v___y_5112_, v___y_5115_);
return v___x_5136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5209_, lean_object* v_dec_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5209_, v_dec_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec_ref(v_a_5211_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5227_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5228_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5229_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5230_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5231_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5227_, v___x_5228_, v___x_5229_, v___x_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
uint8_t v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; 
v___x_5243_ = 0;
v___x_5244_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5234_, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v_____do__lift_5246_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5275_, size_t v_sz_5276_, size_t v_i_5277_, lean_object* v_b_5278_, lean_object* v___y_5279_){
_start:
{
uint8_t v___x_5281_; 
v___x_5281_ = lean_usize_dec_lt(v_i_5277_, v_sz_5276_);
if (v___x_5281_ == 0)
{
lean_object* v___x_5282_; 
v___x_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5282_, 0, v_b_5278_);
return v___x_5282_;
}
else
{
lean_object* v_ref_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v_a_5286_; uint8_t v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; size_t v___x_5320_; size_t v___x_5321_; 
v_ref_5283_ = lean_ctor_get(v___y_5279_, 5);
v___x_5284_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5286_ = lean_array_uget_borrowed(v_as_5275_, v_i_5277_);
v___x_5287_ = 0;
v___x_5288_ = l_Lean_SourceInfo_fromRef(v_ref_5283_, v___x_5287_);
v___x_5289_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5291_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5292_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5288_, 17);
v___x_5293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5288_);
lean_ctor_set(v___x_5293_, 1, v___x_5292_);
v___x_5294_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5288_);
lean_ctor_set(v___x_5295_, 1, v___x_5294_);
v___x_5296_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5289_, v___x_5295_);
v___x_5297_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5288_);
lean_ctor_set(v___x_5298_, 1, v___x_5289_);
lean_ctor_set(v___x_5298_, 2, v___x_5297_);
lean_inc_ref_n(v___x_5298_, 3);
v___x_5299_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5284_, v___x_5298_);
v___x_5300_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5301_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5302_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5286_, 2);
v___x_5303_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5302_, v_a_5286_);
v___x_5304_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5288_);
lean_ctor_set(v___x_5305_, 1, v___x_5304_);
v___x_5306_ = l_Lean_Syntax_node5(v___x_5288_, v___x_5301_, v___x_5303_, v___x_5298_, v___x_5298_, v___x_5305_, v_a_5286_);
v___x_5307_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5300_, v___x_5306_);
v___x_5308_ = l_Lean_Syntax_node4(v___x_5288_, v___x_5291_, v___x_5293_, v___x_5296_, v___x_5299_, v___x_5307_);
v___x_5309_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5288_);
lean_ctor_set(v___x_5310_, 1, v___x_5309_);
v___x_5311_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5289_, v___x_5310_);
v___x_5312_ = l_Lean_Syntax_node2(v___x_5288_, v___x_5290_, v___x_5308_, v___x_5311_);
v___x_5313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5288_);
lean_ctor_set(v___x_5315_, 1, v___x_5314_);
v___x_5316_ = l_Lean_Syntax_node2(v___x_5288_, v___x_5313_, v___x_5315_, v_b_5278_);
v___x_5317_ = l_Lean_Syntax_node2(v___x_5288_, v___x_5290_, v___x_5316_, v___x_5298_);
v___x_5318_ = l_Lean_Syntax_node2(v___x_5288_, v___x_5289_, v___x_5312_, v___x_5317_);
v___x_5319_ = l_Lean_Syntax_node1(v___x_5288_, v___x_5285_, v___x_5318_);
v___x_5320_ = ((size_t)1ULL);
v___x_5321_ = lean_usize_add(v_i_5277_, v___x_5320_);
v_i_5277_ = v___x_5321_;
v_b_5278_ = v___x_5319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5323_, lean_object* v_sz_5324_, lean_object* v_i_5325_, lean_object* v_b_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_){
_start:
{
size_t v_sz_boxed_5329_; size_t v_i_boxed_5330_; lean_object* v_res_5331_; 
v_sz_boxed_5329_ = lean_unbox_usize(v_sz_5324_);
lean_dec(v_sz_5324_);
v_i_boxed_5330_ = lean_unbox_usize(v_i_5325_);
lean_dec(v_i_5325_);
v_res_5331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5323_, v_sz_boxed_5329_, v_i_boxed_5330_, v_b_5326_, v___y_5327_);
lean_dec_ref(v___y_5327_);
lean_dec_ref(v_as_5323_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5332_, size_t v_sz_5333_, size_t v_i_5334_, lean_object* v_b_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
uint8_t v___x_5344_; 
v___x_5344_ = lean_usize_dec_lt(v_i_5334_, v_sz_5333_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; 
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v_b_5335_);
return v___x_5345_;
}
else
{
lean_object* v_ref_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v_a_5349_; uint8_t v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; size_t v___x_5383_; size_t v___x_5384_; lean_object* v___x_5385_; 
v_ref_5346_ = lean_ctor_get(v___y_5341_, 5);
v___x_5347_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5349_ = lean_array_uget_borrowed(v_as_5332_, v_i_5334_);
v___x_5350_ = 0;
v___x_5351_ = l_Lean_SourceInfo_fromRef(v_ref_5346_, v___x_5350_);
v___x_5352_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5354_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5355_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5351_, 17);
v___x_5356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5351_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5351_);
lean_ctor_set(v___x_5358_, 1, v___x_5357_);
v___x_5359_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5352_, v___x_5358_);
v___x_5360_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5351_);
lean_ctor_set(v___x_5361_, 1, v___x_5352_);
lean_ctor_set(v___x_5361_, 2, v___x_5360_);
lean_inc_ref_n(v___x_5361_, 3);
v___x_5362_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5347_, v___x_5361_);
v___x_5363_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5364_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5365_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5349_, 2);
v___x_5366_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5365_, v_a_5349_);
v___x_5367_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5351_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
v___x_5369_ = l_Lean_Syntax_node5(v___x_5351_, v___x_5364_, v___x_5366_, v___x_5361_, v___x_5361_, v___x_5368_, v_a_5349_);
v___x_5370_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5363_, v___x_5369_);
v___x_5371_ = l_Lean_Syntax_node4(v___x_5351_, v___x_5354_, v___x_5356_, v___x_5359_, v___x_5362_, v___x_5370_);
v___x_5372_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5351_);
lean_ctor_set(v___x_5373_, 1, v___x_5372_);
v___x_5374_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5352_, v___x_5373_);
v___x_5375_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5353_, v___x_5371_, v___x_5374_);
v___x_5376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5351_);
lean_ctor_set(v___x_5378_, 1, v___x_5377_);
v___x_5379_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5376_, v___x_5378_, v_b_5335_);
v___x_5380_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5353_, v___x_5379_, v___x_5361_);
v___x_5381_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5352_, v___x_5375_, v___x_5380_);
v___x_5382_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5348_, v___x_5381_);
v___x_5383_ = ((size_t)1ULL);
v___x_5384_ = lean_usize_add(v_i_5334_, v___x_5383_);
v___x_5385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5332_, v_sz_5333_, v___x_5384_, v___x_5382_, v___y_5341_);
return v___x_5385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5386_, lean_object* v_sz_5387_, lean_object* v_i_5388_, lean_object* v_b_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
size_t v_sz_boxed_5398_; size_t v_i_boxed_5399_; lean_object* v_res_5400_; 
v_sz_boxed_5398_ = lean_unbox_usize(v_sz_5387_);
lean_dec(v_sz_5387_);
v_i_boxed_5399_ = lean_unbox_usize(v_i_5388_);
lean_dec(v_i_5388_);
v_res_5400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5386_, v_sz_boxed_5398_, v_i_boxed_5399_, v_b_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec_ref(v_as_5386_);
return v_res_5400_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5440_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5441_ = l_String_toRawSubstring_x27(v___x_5440_);
return v___x_5441_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5455_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5456_ = l_String_toRawSubstring_x27(v___x_5455_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5473_, lean_object* v_dec_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v___x_5483_; uint8_t v___x_5484_; 
v___x_5483_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5473_);
v___x_5484_ = l_Lean_Syntax_isOfKind(v_stx_5473_, v___x_5483_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5485_; 
lean_dec_ref(v_dec_5474_);
lean_dec(v_stx_5473_);
v___x_5485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5485_;
}
else
{
lean_object* v___y_5487_; uint8_t v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v_body_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5573_; uint8_t v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; uint8_t v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v_a_5588_; lean_object* v___y_5602_; uint8_t v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___y_5606_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v_mutTk_x3f_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___x_5718_; lean_object* v___x_5719_; uint8_t v___x_5720_; 
v___x_5718_ = lean_unsigned_to_nat(1u);
v___x_5719_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5718_);
v___x_5720_ = l_Lean_Syntax_isNone(v___x_5719_);
if (v___x_5720_ == 0)
{
uint8_t v___x_5721_; 
lean_inc(v___x_5719_);
v___x_5721_ = l_Lean_Syntax_matchesNull(v___x_5719_, v___x_5718_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5722_; 
lean_dec(v___x_5719_);
lean_dec_ref(v_dec_5474_);
lean_dec(v_stx_5473_);
v___x_5722_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5722_;
}
else
{
lean_object* v___x_5723_; lean_object* v_mutTk_x3f_5724_; lean_object* v___x_5725_; 
v___x_5723_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5724_ = l_Lean_Syntax_getArg(v___x_5719_, v___x_5723_);
lean_dec(v___x_5719_);
v___x_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5725_, 0, v_mutTk_x3f_5724_);
v_mutTk_x3f_5687_ = v___x_5725_;
v___y_5688_ = v_a_5475_;
v___y_5689_ = v_a_5476_;
v___y_5690_ = v_a_5477_;
v___y_5691_ = v_a_5478_;
v___y_5692_ = v_a_5479_;
v___y_5693_ = v_a_5480_;
v___y_5694_ = v_a_5481_;
goto v___jp_5686_;
}
}
else
{
lean_object* v___x_5726_; 
lean_dec(v___x_5719_);
v___x_5726_ = lean_box(0);
v_mutTk_x3f_5687_ = v___x_5726_;
v___y_5688_ = v_a_5475_;
v___y_5689_ = v_a_5476_;
v___y_5690_ = v_a_5477_;
v___y_5691_ = v_a_5478_;
v___y_5692_ = v_a_5479_;
v___y_5693_ = v_a_5480_;
v___y_5694_ = v_a_5481_;
goto v___jp_5686_;
}
v___jp_5486_:
{
lean_object* v_eq_x3f_5500_; 
v_eq_x3f_5500_ = lean_ctor_get(v___y_5491_, 0);
lean_inc(v_eq_x3f_5500_);
lean_dec_ref(v___y_5491_);
if (lean_obj_tag(v_eq_x3f_5500_) == 1)
{
lean_object* v_val_5501_; lean_object* v_ref_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; 
v_val_5501_ = lean_ctor_get(v_eq_x3f_5500_, 0);
lean_inc(v_val_5501_);
lean_dec_ref(v_eq_x3f_5500_);
v_ref_5502_ = lean_ctor_get(v___y_5498_, 5);
v___x_5503_ = l_Lean_SourceInfo_fromRef(v_ref_5502_, v___y_5488_);
v___x_5504_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5505_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5503_, 19);
v___x_5506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5503_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v___x_5507_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5508_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5503_);
lean_ctor_set(v___x_5509_, 1, v___x_5507_);
lean_ctor_set(v___x_5509_, 2, v___x_5508_);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5511_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5512_, 0, v___x_5503_);
lean_ctor_set(v___x_5512_, 1, v___x_5511_);
v___x_5513_ = l_Lean_Syntax_node2(v___x_5503_, v___x_5507_, v_val_5501_, v___x_5512_);
v___x_5514_ = l_Lean_Syntax_node2(v___x_5503_, v___x_5510_, v___x_5513_, v___y_5490_);
v___x_5515_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5507_, v___x_5514_);
v___x_5516_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5503_);
lean_ctor_set(v___x_5517_, 1, v___x_5516_);
v___x_5518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5519_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5503_);
lean_ctor_set(v___x_5521_, 1, v___x_5520_);
v___x_5522_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5507_, v___y_5489_);
v___x_5523_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5507_, v___x_5522_);
v___x_5524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5503_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
lean_inc_ref(v___x_5525_);
lean_inc_ref(v___x_5521_);
v___x_5526_ = l_Lean_Syntax_node4(v___x_5503_, v___x_5519_, v___x_5521_, v___x_5523_, v___x_5525_, v_body_5492_);
v___x_5527_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5529_, 0, v___x_5503_);
lean_ctor_set(v___x_5529_, 1, v___x_5528_);
v___x_5530_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5527_, v___x_5529_);
v___x_5531_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5507_, v___x_5530_);
v___x_5532_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5507_, v___x_5531_);
v___x_5533_ = l_Lean_Syntax_node4(v___x_5503_, v___x_5519_, v___x_5521_, v___x_5532_, v___x_5525_, v___y_5487_);
v___x_5534_ = l_Lean_Syntax_node2(v___x_5503_, v___x_5507_, v___x_5526_, v___x_5533_);
v___x_5535_ = l_Lean_Syntax_node1(v___x_5503_, v___x_5518_, v___x_5534_);
lean_inc_ref_n(v___x_5509_, 2);
v___x_5536_ = l_Lean_Syntax_node7(v___x_5503_, v___x_5504_, v___x_5506_, v___x_5509_, v___x_5509_, v___x_5509_, v___x_5515_, v___x_5517_, v___x_5535_);
v___x_5537_ = l_Lean_Elab_Do_elabDoElem(v___x_5536_, v_dec_5474_, v___x_5484_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
return v___x_5537_;
}
else
{
lean_object* v_ref_5538_; lean_object* v___x_5539_; lean_object* v_a_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; 
lean_dec(v_eq_x3f_5500_);
v_ref_5538_ = lean_ctor_get(v___y_5498_, 5);
v___x_5539_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5538_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
lean_inc_n(v_a_5540_, 18);
lean_dec_ref(v___x_5539_);
v___x_5541_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5542_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5543_, 0, v_a_5540_);
lean_ctor_set(v___x_5543_, 1, v___x_5542_);
v___x_5544_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5545_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5546_, 0, v_a_5540_);
lean_ctor_set(v___x_5546_, 1, v___x_5544_);
lean_ctor_set(v___x_5546_, 2, v___x_5545_);
v___x_5547_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5546_, 3);
v___x_5548_ = l_Lean_Syntax_node2(v_a_5540_, v___x_5547_, v___x_5546_, v___y_5490_);
v___x_5549_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5544_, v___x_5548_);
v___x_5550_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5551_, 0, v_a_5540_);
lean_ctor_set(v___x_5551_, 1, v___x_5550_);
v___x_5552_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5553_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5554_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5555_, 0, v_a_5540_);
lean_ctor_set(v___x_5555_, 1, v___x_5554_);
v___x_5556_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5544_, v___y_5489_);
v___x_5557_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5544_, v___x_5556_);
v___x_5558_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5559_, 0, v_a_5540_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
lean_inc_ref(v___x_5559_);
lean_inc_ref(v___x_5555_);
v___x_5560_ = l_Lean_Syntax_node4(v_a_5540_, v___x_5553_, v___x_5555_, v___x_5557_, v___x_5559_, v_body_5492_);
v___x_5561_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5562_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5563_, 0, v_a_5540_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___x_5564_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5561_, v___x_5563_);
v___x_5565_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5544_, v___x_5564_);
v___x_5566_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5544_, v___x_5565_);
v___x_5567_ = l_Lean_Syntax_node4(v_a_5540_, v___x_5553_, v___x_5555_, v___x_5566_, v___x_5559_, v___y_5487_);
v___x_5568_ = l_Lean_Syntax_node2(v_a_5540_, v___x_5544_, v___x_5560_, v___x_5567_);
v___x_5569_ = l_Lean_Syntax_node1(v_a_5540_, v___x_5552_, v___x_5568_);
v___x_5570_ = l_Lean_Syntax_node7(v_a_5540_, v___x_5541_, v___x_5543_, v___x_5546_, v___x_5546_, v___x_5546_, v___x_5549_, v___x_5551_, v___x_5569_);
v___x_5571_ = l_Lean_Elab_Do_elabDoElem(v___x_5570_, v_dec_5474_, v___x_5484_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
return v___x_5571_;
}
}
v___jp_5572_:
{
if (lean_obj_tag(v___y_5587_) == 0)
{
lean_dec_ref(v___y_5585_);
v___y_5487_ = v___y_5582_;
v___y_5488_ = v___y_5584_;
v___y_5489_ = v___y_5576_;
v___y_5490_ = v___y_5579_;
v___y_5491_ = v___y_5580_;
v_body_5492_ = v_a_5588_;
v___y_5493_ = v___y_5578_;
v___y_5494_ = v___y_5577_;
v___y_5495_ = v___y_5581_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5575_;
v___y_5498_ = v___y_5573_;
v___y_5499_ = v___y_5586_;
goto v___jp_5486_;
}
else
{
lean_dec_ref(v___y_5587_);
if (v___y_5574_ == 0)
{
lean_dec_ref(v___y_5585_);
v___y_5487_ = v___y_5582_;
v___y_5488_ = v___y_5584_;
v___y_5489_ = v___y_5576_;
v___y_5490_ = v___y_5579_;
v___y_5491_ = v___y_5580_;
v_body_5492_ = v_a_5588_;
v___y_5493_ = v___y_5578_;
v___y_5494_ = v___y_5577_;
v___y_5495_ = v___y_5581_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5575_;
v___y_5498_ = v___y_5573_;
v___y_5499_ = v___y_5586_;
goto v___jp_5486_;
}
else
{
size_t v_sz_5589_; size_t v___x_5590_; lean_object* v___x_5591_; 
v_sz_5589_ = lean_array_size(v___y_5585_);
v___x_5590_ = ((size_t)0ULL);
v___x_5591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5585_, v_sz_5589_, v___x_5590_, v_a_5588_, v___y_5578_, v___y_5577_, v___y_5581_, v___y_5583_, v___y_5575_, v___y_5573_, v___y_5586_);
lean_dec_ref(v___y_5585_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_a_5592_);
lean_dec_ref(v___x_5591_);
v___y_5487_ = v___y_5582_;
v___y_5488_ = v___y_5584_;
v___y_5489_ = v___y_5576_;
v___y_5490_ = v___y_5579_;
v___y_5491_ = v___y_5580_;
v_body_5492_ = v_a_5592_;
v___y_5493_ = v___y_5578_;
v___y_5494_ = v___y_5577_;
v___y_5495_ = v___y_5581_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5575_;
v___y_5498_ = v___y_5573_;
v___y_5499_ = v___y_5586_;
goto v___jp_5486_;
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5580_);
lean_dec(v___y_5579_);
lean_dec(v___y_5576_);
lean_dec_ref(v_dec_5474_);
v_a_5593_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5591_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5591_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
}
}
}
v___jp_5601_:
{
uint8_t v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5616_ = 0;
v___x_5617_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5618_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5612_, v___y_5614_, v___x_5617_, v___y_5606_, v___y_5609_, v___y_5611_, v___y_5604_, v___y_5602_, v___y_5613_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_object* v_a_5619_; lean_object* v___x_5620_; 
v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
lean_inc(v_a_5619_);
lean_dec_ref(v___x_5618_);
v___x_5620_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5619_, v___y_5607_, v___y_5606_, v___y_5609_, v___y_5611_, v___y_5604_, v___y_5602_, v___y_5613_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v___x_5621_; 
lean_dec_ref(v___x_5620_);
lean_inc(v___y_5605_);
v___x_5621_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5605_, v___y_5606_, v___y_5609_, v___y_5611_, v___y_5604_, v___y_5602_, v___y_5613_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_a_5622_ = lean_ctor_get(v___x_5621_, 0);
lean_inc(v_a_5622_);
lean_dec_ref(v___x_5621_);
lean_inc(v___y_5614_);
v___x_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5623_, 0, v___y_5614_);
v___x_5624_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5623_, v_a_5622_, v___y_5607_, v___y_5606_, v___y_5609_, v___y_5611_, v___y_5604_, v___y_5602_, v___y_5613_);
lean_dec_ref(v___x_5623_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_dec_ref(v___x_5624_);
if (lean_obj_tag(v___y_5615_) == 0)
{
lean_object* v_ref_5625_; lean_object* v_quotContext_5626_; lean_object* v_currMacroScope_5627_; lean_object* v___x_5628_; lean_object* v_a_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; 
v_ref_5625_ = lean_ctor_get(v___y_5602_, 5);
v_quotContext_5626_ = lean_ctor_get(v___y_5602_, 10);
v_currMacroScope_5627_ = lean_ctor_get(v___y_5602_, 11);
v___x_5628_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5625_, v___y_5607_, v___y_5606_, v___y_5609_, v___y_5611_, v___y_5604_, v___y_5602_, v___y_5613_);
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc_n(v_a_5629_, 9);
lean_dec_ref(v___x_5628_);
v___x_5630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5631_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5633_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5634_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5635_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5636_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5627_, 2);
lean_inc_n(v_quotContext_5626_, 2);
v___x_5637_ = l_Lean_addMacroScope(v_quotContext_5626_, v___x_5636_, v_currMacroScope_5627_);
v___x_5638_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5639_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5639_, 0, v_a_5629_);
lean_ctor_set(v___x_5639_, 1, v___x_5635_);
lean_ctor_set(v___x_5639_, 2, v___x_5637_);
lean_ctor_set(v___x_5639_, 3, v___x_5638_);
v___x_5640_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5642_ = l_Lean_addMacroScope(v_quotContext_5626_, v___x_5641_, v_currMacroScope_5627_);
v___x_5643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5644_, 0, v_a_5629_);
lean_ctor_set(v___x_5644_, 1, v___x_5640_);
lean_ctor_set(v___x_5644_, 2, v___x_5642_);
lean_ctor_set(v___x_5644_, 3, v___x_5643_);
v___x_5645_ = l_Lean_Syntax_node1(v_a_5629_, v___x_5631_, v___x_5644_);
v___x_5646_ = l_Lean_Syntax_node2(v_a_5629_, v___x_5634_, v___x_5639_, v___x_5645_);
v___x_5647_ = l_Lean_Syntax_node1(v_a_5629_, v___x_5633_, v___x_5646_);
v___x_5648_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5649_, 0, v_a_5629_);
lean_ctor_set(v___x_5649_, 1, v___x_5631_);
lean_ctor_set(v___x_5649_, 2, v___x_5648_);
v___x_5650_ = l_Lean_Syntax_node2(v_a_5629_, v___x_5632_, v___x_5647_, v___x_5649_);
v___x_5651_ = l_Lean_Syntax_node1(v_a_5629_, v___x_5631_, v___x_5650_);
v___x_5652_ = l_Lean_Syntax_node1(v_a_5629_, v___x_5630_, v___x_5651_);
v___y_5573_ = v___y_5602_;
v___y_5574_ = v___y_5603_;
v___y_5575_ = v___y_5604_;
v___y_5576_ = v___y_5605_;
v___y_5577_ = v___y_5606_;
v___y_5578_ = v___y_5607_;
v___y_5579_ = v___y_5608_;
v___y_5580_ = v_a_5619_;
v___y_5581_ = v___y_5609_;
v___y_5582_ = v___y_5610_;
v___y_5583_ = v___y_5611_;
v___y_5584_ = v___x_5616_;
v___y_5585_ = v_a_5622_;
v___y_5586_ = v___y_5613_;
v___y_5587_ = v___y_5614_;
v_a_5588_ = v___x_5652_;
goto v___jp_5572_;
}
else
{
lean_object* v_val_5653_; 
v_val_5653_ = lean_ctor_get(v___y_5615_, 0);
lean_inc(v_val_5653_);
lean_dec_ref(v___y_5615_);
v___y_5573_ = v___y_5602_;
v___y_5574_ = v___y_5603_;
v___y_5575_ = v___y_5604_;
v___y_5576_ = v___y_5605_;
v___y_5577_ = v___y_5606_;
v___y_5578_ = v___y_5607_;
v___y_5579_ = v___y_5608_;
v___y_5580_ = v_a_5619_;
v___y_5581_ = v___y_5609_;
v___y_5582_ = v___y_5610_;
v___y_5583_ = v___y_5611_;
v___y_5584_ = v___x_5616_;
v___y_5585_ = v_a_5622_;
v___y_5586_ = v___y_5613_;
v___y_5587_ = v___y_5614_;
v_a_5588_ = v_val_5653_;
goto v___jp_5572_;
}
}
else
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
lean_dec(v_a_5622_);
lean_dec(v_a_5619_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec(v___y_5610_);
lean_dec(v___y_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v_dec_5474_);
v_a_5654_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5624_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5624_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5657_ == 0)
{
v___x_5659_ = v___x_5656_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
else
{
lean_object* v_a_5662_; lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5669_; 
lean_dec(v_a_5619_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec(v___y_5610_);
lean_dec(v___y_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v_dec_5474_);
v_a_5662_ = lean_ctor_get(v___x_5621_, 0);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5664_ = v___x_5621_;
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
else
{
lean_inc(v_a_5662_);
lean_dec(v___x_5621_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5669_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5667_; 
if (v_isShared_5665_ == 0)
{
v___x_5667_ = v___x_5664_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
}
else
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5677_; 
lean_dec(v_a_5619_);
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec(v___y_5610_);
lean_dec(v___y_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v_dec_5474_);
v_a_5670_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5672_ = v___x_5620_;
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5620_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5675_; 
if (v_isShared_5673_ == 0)
{
v___x_5675_ = v___x_5672_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
}
else
{
lean_object* v_a_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5685_; 
lean_dec(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec(v___y_5610_);
lean_dec(v___y_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v_dec_5474_);
v_a_5678_ = lean_ctor_get(v___x_5618_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v___x_5618_);
if (v_isSharedCheck_5685_ == 0)
{
v___x_5680_ = v___x_5618_;
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_a_5678_);
lean_dec(v___x_5618_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v___x_5683_; 
if (v_isShared_5681_ == 0)
{
v___x_5683_ = v___x_5680_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5684_; 
v_reuseFailAlloc_5684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
v___x_5683_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
return v___x_5683_;
}
}
}
}
v___jp_5686_:
{
lean_object* v___x_5695_; lean_object* v_cfg_5696_; lean_object* v___x_5697_; uint8_t v___x_5698_; 
v___x_5695_ = lean_unsigned_to_nat(2u);
v_cfg_5696_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5695_);
v___x_5697_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5696_);
v___x_5698_ = l_Lean_Syntax_isOfKind(v_cfg_5696_, v___x_5697_);
if (v___x_5698_ == 0)
{
lean_object* v___x_5699_; 
lean_dec(v_cfg_5696_);
lean_dec(v_mutTk_x3f_5687_);
lean_dec_ref(v_dec_5474_);
lean_dec(v_stx_5473_);
v___x_5699_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5699_;
}
else
{
lean_object* v___x_5700_; lean_object* v_pattern_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5700_ = lean_unsigned_to_nat(3u);
v_pattern_5701_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5700_);
v___x_5702_ = lean_unsigned_to_nat(5u);
v___x_5703_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5702_);
v___x_5704_ = lean_unsigned_to_nat(7u);
v___x_5705_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5704_);
v___x_5706_ = lean_unsigned_to_nat(8u);
v___x_5707_ = l_Lean_Syntax_getArg(v_stx_5473_, v___x_5706_);
lean_dec(v_stx_5473_);
v___x_5708_ = l_Lean_Syntax_getOptional_x3f(v___x_5707_);
lean_dec(v___x_5707_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v___x_5709_; 
v___x_5709_ = lean_box(0);
v___y_5602_ = v___y_5693_;
v___y_5603_ = v___x_5698_;
v___y_5604_ = v___y_5692_;
v___y_5605_ = v_pattern_5701_;
v___y_5606_ = v___y_5689_;
v___y_5607_ = v___y_5688_;
v___y_5608_ = v___x_5703_;
v___y_5609_ = v___y_5690_;
v___y_5610_ = v___x_5705_;
v___y_5611_ = v___y_5691_;
v___y_5612_ = v_cfg_5696_;
v___y_5613_ = v___y_5694_;
v___y_5614_ = v_mutTk_x3f_5687_;
v___y_5615_ = v___x_5709_;
goto v___jp_5601_;
}
else
{
lean_object* v_val_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
v_val_5710_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___x_5708_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_val_5710_);
lean_dec(v___x_5708_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_val_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
v___y_5602_ = v___y_5693_;
v___y_5603_ = v___x_5698_;
v___y_5604_ = v___y_5692_;
v___y_5605_ = v_pattern_5701_;
v___y_5606_ = v___y_5689_;
v___y_5607_ = v___y_5688_;
v___y_5608_ = v___x_5703_;
v___y_5609_ = v___y_5690_;
v___y_5610_ = v___x_5705_;
v___y_5611_ = v___y_5691_;
v___y_5612_ = v_cfg_5696_;
v___y_5613_ = v___y_5694_;
v___y_5614_ = v_mutTk_x3f_5687_;
v___y_5615_ = v___x_5715_;
goto v___jp_5601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5727_, lean_object* v_dec_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_){
_start:
{
lean_object* v_res_5737_; 
v_res_5737_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5727_, v_dec_5728_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec_ref(v_a_5729_);
return v_res_5737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5738_, size_t v_sz_5739_, size_t v_i_5740_, lean_object* v_b_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
lean_object* v___x_5750_; 
v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5738_, v_sz_5739_, v_i_5740_, v_b_5741_, v___y_5747_);
return v___x_5750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5751_, lean_object* v_sz_5752_, lean_object* v_i_5753_, lean_object* v_b_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
size_t v_sz_boxed_5763_; size_t v_i_boxed_5764_; lean_object* v_res_5765_; 
v_sz_boxed_5763_ = lean_unbox_usize(v_sz_5752_);
lean_dec(v_sz_5752_);
v_i_boxed_5764_ = lean_unbox_usize(v_i_5753_);
lean_dec(v_i_5753_);
v_res_5765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5751_, v_sz_boxed_5763_, v_i_boxed_5764_, v_b_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___y_5757_);
lean_dec_ref(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec_ref(v_as_5751_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5773_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5774_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5775_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5776_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5777_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5773_, v___x_5774_, v___x_5775_, v___x_5776_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5778_){
_start:
{
lean_object* v_res_5779_; 
v_res_5779_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5779_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5787_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5788_ = l_Lean_stringToMessageData(v___x_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5789_, lean_object* v_dec_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v___x_5799_; uint8_t v___x_5800_; 
v___x_5799_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5789_);
v___x_5800_ = l_Lean_Syntax_isOfKind(v_stx_5789_, v___x_5799_);
if (v___x_5800_ == 0)
{
lean_object* v___x_5801_; 
lean_dec_ref(v_dec_5790_);
lean_dec(v_stx_5789_);
v___x_5801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5801_;
}
else
{
lean_object* v___x_5802_; lean_object* v_tk_5803_; lean_object* v___y_5805_; lean_object* v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5808_; lean_object* v___y_5809_; lean_object* v___y_5810_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5838_; lean_object* v___y_5839_; lean_object* v___y_5840_; lean_object* v___y_5841_; lean_object* v___y_5842_; uint8_t v___y_5843_; lean_object* v___y_5844_; lean_object* v___y_5845_; lean_object* v___y_5846_; lean_object* v___y_5847_; lean_object* v___y_5848_; lean_object* v___y_5849_; uint8_t v___y_5850_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; lean_object* v___y_5857_; uint8_t v___y_5858_; lean_object* v___y_5859_; lean_object* v___y_5860_; lean_object* v___y_5861_; lean_object* v___y_5862_; lean_object* v___y_5863_; lean_object* v___y_5864_; uint8_t v___y_5865_; lean_object* v_mutTk_x3f_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; lean_object* v___y_5875_; lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5802_ = lean_unsigned_to_nat(0u);
v_tk_5803_ = l_Lean_Syntax_getArg(v_stx_5789_, v___x_5802_);
v___x_5905_ = lean_unsigned_to_nat(1u);
v___x_5906_ = l_Lean_Syntax_getArg(v_stx_5789_, v___x_5905_);
v___x_5907_ = l_Lean_Syntax_isNone(v___x_5906_);
if (v___x_5907_ == 0)
{
uint8_t v___x_5908_; 
lean_inc(v___x_5906_);
v___x_5908_ = l_Lean_Syntax_matchesNull(v___x_5906_, v___x_5905_);
if (v___x_5908_ == 0)
{
lean_object* v___x_5909_; 
lean_dec(v___x_5906_);
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
lean_dec(v_stx_5789_);
v___x_5909_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5909_;
}
else
{
lean_object* v_mutTk_x3f_5910_; lean_object* v___x_5911_; 
v_mutTk_x3f_5910_ = l_Lean_Syntax_getArg(v___x_5906_, v___x_5802_);
lean_dec(v___x_5906_);
v___x_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5911_, 0, v_mutTk_x3f_5910_);
v_mutTk_x3f_5868_ = v___x_5911_;
v___y_5869_ = v_a_5791_;
v___y_5870_ = v_a_5792_;
v___y_5871_ = v_a_5793_;
v___y_5872_ = v_a_5794_;
v___y_5873_ = v_a_5795_;
v___y_5874_ = v_a_5796_;
v___y_5875_ = v_a_5797_;
goto v___jp_5867_;
}
}
else
{
lean_object* v___x_5912_; 
lean_dec(v___x_5906_);
v___x_5912_ = lean_box(0);
v_mutTk_x3f_5868_ = v___x_5912_;
v___y_5869_ = v_a_5791_;
v___y_5870_ = v_a_5792_;
v___y_5871_ = v_a_5793_;
v___y_5872_ = v_a_5794_;
v___y_5873_ = v_a_5795_;
v___y_5874_ = v_a_5796_;
v___y_5875_ = v_a_5797_;
goto v___jp_5867_;
}
v___jp_5804_:
{
lean_object* v___x_5814_; lean_object* v___x_5815_; 
v___x_5814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5814_, 0, v___y_5806_);
v___x_5815_ = l_Lean_Elab_Do_elabDoArrow(v___x_5814_, v___y_5805_, v_tk_5803_, v_dec_5790_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
lean_dec(v_tk_5803_);
return v___x_5815_;
}
v___jp_5816_:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v_a_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5836_; 
lean_dec(v___y_5824_);
lean_dec(v___y_5817_);
v___x_5827_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5828_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5825_, v___x_5827_, v___y_5818_, v___y_5823_, v___y_5822_, v___y_5820_);
lean_dec(v___y_5825_);
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_5836_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_5836_ == 0)
{
v___x_5831_ = v___x_5828_;
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_a_5829_);
lean_dec(v___x_5828_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5834_; 
if (v_isShared_5832_ == 0)
{
v___x_5834_ = v___x_5831_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5829_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
v___jp_5837_:
{
if (v___y_5850_ == 0)
{
lean_object* v_eq_x3f_5851_; 
v_eq_x3f_5851_ = lean_ctor_get(v___y_5838_, 0);
lean_inc(v_eq_x3f_5851_);
lean_dec_ref(v___y_5838_);
if (lean_obj_tag(v_eq_x3f_5851_) == 0)
{
lean_dec(v___y_5841_);
v___y_5805_ = v___y_5845_;
v___y_5806_ = v___y_5849_;
v___y_5807_ = v___y_5842_;
v___y_5808_ = v___y_5847_;
v___y_5809_ = v___y_5846_;
v___y_5810_ = v___y_5844_;
v___y_5811_ = v___y_5848_;
v___y_5812_ = v___y_5840_;
v___y_5813_ = v___y_5839_;
goto v___jp_5804_;
}
else
{
lean_dec_ref(v_eq_x3f_5851_);
if (v___y_5843_ == 0)
{
lean_dec(v___y_5841_);
v___y_5805_ = v___y_5845_;
v___y_5806_ = v___y_5849_;
v___y_5807_ = v___y_5842_;
v___y_5808_ = v___y_5847_;
v___y_5809_ = v___y_5846_;
v___y_5810_ = v___y_5844_;
v___y_5811_ = v___y_5848_;
v___y_5812_ = v___y_5840_;
v___y_5813_ = v___y_5839_;
goto v___jp_5804_;
}
else
{
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
v___y_5817_ = v___y_5845_;
v___y_5818_ = v___y_5844_;
v___y_5819_ = v___y_5846_;
v___y_5820_ = v___y_5839_;
v___y_5821_ = v___y_5847_;
v___y_5822_ = v___y_5840_;
v___y_5823_ = v___y_5848_;
v___y_5824_ = v___y_5849_;
v___y_5825_ = v___y_5841_;
v___y_5826_ = v___y_5842_;
goto v___jp_5816_;
}
}
}
else
{
lean_dec_ref(v___y_5838_);
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
v___y_5817_ = v___y_5845_;
v___y_5818_ = v___y_5844_;
v___y_5819_ = v___y_5846_;
v___y_5820_ = v___y_5839_;
v___y_5821_ = v___y_5847_;
v___y_5822_ = v___y_5840_;
v___y_5823_ = v___y_5848_;
v___y_5824_ = v___y_5849_;
v___y_5825_ = v___y_5841_;
v___y_5826_ = v___y_5842_;
goto v___jp_5816_;
}
}
v___jp_5852_:
{
if (v___y_5865_ == 0)
{
uint8_t v_zeta_5866_; 
v_zeta_5866_ = lean_ctor_get_uint8(v___y_5853_, sizeof(void*)*1 + 2);
v___y_5838_ = v___y_5853_;
v___y_5839_ = v___y_5854_;
v___y_5840_ = v___y_5855_;
v___y_5841_ = v___y_5856_;
v___y_5842_ = v___y_5857_;
v___y_5843_ = v___y_5858_;
v___y_5844_ = v___y_5859_;
v___y_5845_ = v___y_5860_;
v___y_5846_ = v___y_5861_;
v___y_5847_ = v___y_5862_;
v___y_5848_ = v___y_5863_;
v___y_5849_ = v___y_5864_;
v___y_5850_ = v_zeta_5866_;
goto v___jp_5837_;
}
else
{
v___y_5838_ = v___y_5853_;
v___y_5839_ = v___y_5854_;
v___y_5840_ = v___y_5855_;
v___y_5841_ = v___y_5856_;
v___y_5842_ = v___y_5857_;
v___y_5843_ = v___y_5858_;
v___y_5844_ = v___y_5859_;
v___y_5845_ = v___y_5860_;
v___y_5846_ = v___y_5861_;
v___y_5847_ = v___y_5862_;
v___y_5848_ = v___y_5863_;
v___y_5849_ = v___y_5864_;
v___y_5850_ = v___x_5800_;
goto v___jp_5837_;
}
}
v___jp_5867_:
{
lean_object* v___x_5876_; lean_object* v_cfg_5877_; lean_object* v___x_5878_; uint8_t v___x_5879_; 
v___x_5876_ = lean_unsigned_to_nat(2u);
v_cfg_5877_ = l_Lean_Syntax_getArg(v_stx_5789_, v___x_5876_);
v___x_5878_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5877_);
v___x_5879_ = l_Lean_Syntax_isOfKind(v_cfg_5877_, v___x_5878_);
if (v___x_5879_ == 0)
{
lean_object* v___x_5880_; 
lean_dec(v_cfg_5877_);
lean_dec(v_mutTk_x3f_5868_);
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
lean_dec(v_stx_5789_);
v___x_5880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5880_;
}
else
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5877_);
v___x_5882_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5877_, v_mutTk_x3f_5868_, v___x_5881_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
if (lean_obj_tag(v___x_5882_) == 0)
{
lean_object* v_a_5883_; lean_object* v___x_5884_; 
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
lean_inc(v_a_5883_);
lean_dec_ref(v___x_5882_);
v___x_5884_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5883_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
if (lean_obj_tag(v___x_5884_) == 0)
{
uint8_t v_nondep_5885_; uint8_t v_usedOnly_5886_; lean_object* v___x_5887_; lean_object* v_decl_5888_; 
lean_dec_ref(v___x_5884_);
v_nondep_5885_ = lean_ctor_get_uint8(v_a_5883_, sizeof(void*)*1);
v_usedOnly_5886_ = lean_ctor_get_uint8(v_a_5883_, sizeof(void*)*1 + 1);
v___x_5887_ = lean_unsigned_to_nat(3u);
v_decl_5888_ = l_Lean_Syntax_getArg(v_stx_5789_, v___x_5887_);
lean_dec(v_stx_5789_);
if (v_nondep_5885_ == 0)
{
v___y_5853_ = v_a_5883_;
v___y_5854_ = v___y_5875_;
v___y_5855_ = v___y_5874_;
v___y_5856_ = v_cfg_5877_;
v___y_5857_ = v___y_5869_;
v___y_5858_ = v___x_5879_;
v___y_5859_ = v___y_5872_;
v___y_5860_ = v_decl_5888_;
v___y_5861_ = v___y_5871_;
v___y_5862_ = v___y_5870_;
v___y_5863_ = v___y_5873_;
v___y_5864_ = v_mutTk_x3f_5868_;
v___y_5865_ = v_usedOnly_5886_;
goto v___jp_5852_;
}
else
{
v___y_5853_ = v_a_5883_;
v___y_5854_ = v___y_5875_;
v___y_5855_ = v___y_5874_;
v___y_5856_ = v_cfg_5877_;
v___y_5857_ = v___y_5869_;
v___y_5858_ = v___x_5879_;
v___y_5859_ = v___y_5872_;
v___y_5860_ = v_decl_5888_;
v___y_5861_ = v___y_5871_;
v___y_5862_ = v___y_5870_;
v___y_5863_ = v___y_5873_;
v___y_5864_ = v_mutTk_x3f_5868_;
v___y_5865_ = v___x_5800_;
goto v___jp_5852_;
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec(v_a_5883_);
lean_dec(v_cfg_5877_);
lean_dec(v_mutTk_x3f_5868_);
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
lean_dec(v_stx_5789_);
v_a_5889_ = lean_ctor_get(v___x_5884_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5884_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5884_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5884_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec(v_cfg_5877_);
lean_dec(v_mutTk_x3f_5868_);
lean_dec(v_tk_5803_);
lean_dec_ref(v_dec_5790_);
lean_dec(v_stx_5789_);
v_a_5897_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5882_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5882_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5913_, lean_object* v_dec_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5913_, v_dec_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
lean_dec_ref(v_a_5916_);
lean_dec_ref(v_a_5915_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5931_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5932_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5933_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5934_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5935_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5931_, v___x_5932_, v___x_5933_, v___x_5934_);
return v___x_5935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5936_){
_start:
{
lean_object* v_res_5937_; 
v_res_5937_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5944_, lean_object* v_dec_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_){
_start:
{
lean_object* v___x_5954_; uint8_t v___x_5955_; 
v___x_5954_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5944_);
v___x_5955_ = l_Lean_Syntax_isOfKind(v_stx_5944_, v___x_5954_);
if (v___x_5955_ == 0)
{
lean_object* v___x_5956_; 
lean_dec_ref(v_dec_5945_);
lean_dec(v_stx_5944_);
v___x_5956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5956_;
}
else
{
lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; uint8_t v___x_5960_; 
v___x_5957_ = lean_unsigned_to_nat(0u);
v___x_5958_ = l_Lean_Syntax_getArg(v_stx_5944_, v___x_5957_);
lean_dec(v_stx_5944_);
v___x_5959_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5958_);
v___x_5960_ = l_Lean_Syntax_isOfKind(v___x_5958_, v___x_5959_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5958_);
v___x_5962_ = l_Lean_Syntax_isOfKind(v___x_5958_, v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; 
lean_dec(v___x_5958_);
lean_dec_ref(v_dec_5945_);
v___x_5963_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5963_;
}
else
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = lean_box(2);
lean_inc(v___x_5958_);
v___x_5965_ = l_Lean_Elab_Do_elabDoArrow(v___x_5964_, v___x_5958_, v___x_5958_, v_dec_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
lean_dec(v___x_5958_);
return v___x_5965_;
}
}
else
{
lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5966_ = lean_box(2);
lean_inc(v___x_5958_);
v___x_5967_ = l_Lean_Elab_Do_elabDoArrow(v___x_5966_, v___x_5958_, v___x_5958_, v_dec_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
lean_dec(v___x_5958_);
return v___x_5967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5968_, lean_object* v_dec_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_){
_start:
{
lean_object* v_res_5978_; 
v_res_5978_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5968_, v_dec_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_);
lean_dec(v_a_5976_);
lean_dec_ref(v_a_5975_);
lean_dec(v_a_5974_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec_ref(v_a_5971_);
lean_dec_ref(v_a_5970_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5986_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5987_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5988_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5989_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5990_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5986_, v___x_5987_, v___x_5988_, v___x_5989_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5991_){
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5992_;
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
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
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
