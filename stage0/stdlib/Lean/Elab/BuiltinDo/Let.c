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
lean_object* v___x_83_; lean_object* v_infoState_84_; lean_object* v_env_85_; lean_object* v_nextMacroScope_86_; lean_object* v_ngen_87_; lean_object* v_auxDeclNGen_88_; lean_object* v_traceState_89_; lean_object* v_cache_90_; lean_object* v_messages_91_; lean_object* v_snapshotTasks_92_; lean_object* v_newDecls_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_115_; 
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
v_newDecls_93_ = lean_ctor_get(v___x_83_, 9);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_115_ == 0)
{
v___x_95_ = v___x_83_;
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_newDecls_93_);
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
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v_enabled_97_; lean_object* v_assignment_98_; lean_object* v_lazyAssignment_99_; lean_object* v_trees_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_114_; 
v_enabled_97_ = lean_ctor_get_uint8(v_infoState_84_, sizeof(void*)*3);
v_assignment_98_ = lean_ctor_get(v_infoState_84_, 0);
v_lazyAssignment_99_ = lean_ctor_get(v_infoState_84_, 1);
v_trees_100_ = lean_ctor_get(v_infoState_84_, 2);
v_isSharedCheck_114_ = !lean_is_exclusive(v_infoState_84_);
if (v_isSharedCheck_114_ == 0)
{
v___x_102_ = v_infoState_84_;
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_trees_100_);
lean_inc(v_lazyAssignment_99_);
lean_inc(v_assignment_98_);
lean_dec(v_infoState_84_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_114_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_PersistentArray_push___redArg(v_trees_100_, v_t_75_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_assignment_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_lazyAssignment_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v___x_104_);
lean_ctor_set_uint8(v_reuseFailAlloc_113_, sizeof(void*)*3, v_enabled_97_);
v___x_106_ = v_reuseFailAlloc_113_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 7, v___x_106_);
v___x_108_ = v___x_95_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_env_85_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_nextMacroScope_86_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_ngen_87_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_auxDeclNGen_88_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_traceState_89_);
lean_ctor_set(v_reuseFailAlloc_112_, 5, v_cache_90_);
lean_ctor_set(v_reuseFailAlloc_112_, 6, v_messages_91_);
lean_ctor_set(v_reuseFailAlloc_112_, 7, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_112_, 8, v_snapshotTasks_92_);
lean_ctor_set(v_reuseFailAlloc_112_, 9, v_newDecls_93_);
v___x_108_ = v_reuseFailAlloc_112_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_st_ref_set(v___y_76_, v___x_108_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg___boxed(lean_object* v_t_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v_t_116_, v___y_117_);
lean_dec(v___y_117_);
return v_res_119_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(32u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1(void){
_start:
{
size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_123_ = ((size_t)5ULL);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_unsigned_to_nat(32u);
v___x_126_ = lean_mk_empty_array_with_capacity(v___x_125_);
v___x_127_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__0);
v___x_128_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_124_);
lean_ctor_set(v___x_128_, 3, v___x_124_);
lean_ctor_set_usize(v___x_128_, 4, v___x_123_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(lean_object* v_t_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_infoState_139_; uint8_t v_enabled_140_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_infoState_139_ = lean_ctor_get(v___x_138_, 7);
lean_inc_ref(v_infoState_139_);
lean_dec(v___x_138_);
v_enabled_140_ = lean_ctor_get_uint8(v_infoState_139_, sizeof(void*)*3);
lean_dec_ref(v_infoState_139_);
if (v_enabled_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v_t_129_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v_t_129_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v___x_144_, v___y_136_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___boxed(lean_object* v_t_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v_t_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v_key_159_; lean_object* v_value_160_; lean_object* v_tail_161_; uint8_t v___x_162_; 
v_key_159_ = lean_ctor_get(v_x_157_, 0);
v_value_160_ = lean_ctor_get(v_x_157_, 1);
v_tail_161_ = lean_ctor_get(v_x_157_, 2);
v___x_162_ = lean_name_eq(v_key_159_, v_a_156_);
if (v___x_162_ == 0)
{
v_x_157_ = v_tail_161_;
goto _start;
}
else
{
lean_object* v___x_164_; 
lean_inc(v_value_160_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_value_160_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg___boxed(lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_165_, v_x_166_);
lean_dec(v_x_166_);
lean_dec(v_a_165_);
return v_res_167_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; uint64_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1723u);
v___x_169_ = lean_uint64_of_nat(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_buckets_172_; lean_object* v___x_173_; uint64_t v___y_175_; 
v_buckets_172_ = lean_ctor_get(v_m_170_, 1);
v___x_173_ = lean_array_get_size(v_buckets_172_);
if (lean_obj_tag(v_a_171_) == 0)
{
uint64_t v___x_189_; 
v___x_189_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___closed__0);
v___y_175_ = v___x_189_;
goto v___jp_174_;
}
else
{
uint64_t v_hash_190_; 
v_hash_190_ = lean_ctor_get_uint64(v_a_171_, sizeof(void*)*2);
v___y_175_ = v_hash_190_;
goto v___jp_174_;
}
v___jp_174_:
{
uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v_fold_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_176_ = 32ULL;
v___x_177_ = lean_uint64_shift_right(v___y_175_, v___x_176_);
v_fold_178_ = lean_uint64_xor(v___y_175_, v___x_177_);
v___x_179_ = 16ULL;
v___x_180_ = lean_uint64_shift_right(v_fold_178_, v___x_179_);
v___x_181_ = lean_uint64_xor(v_fold_178_, v___x_180_);
v___x_182_ = lean_uint64_to_usize(v___x_181_);
v___x_183_ = lean_usize_of_nat(v___x_173_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_sub(v___x_183_, v___x_184_);
v___x_186_ = lean_usize_land(v___x_182_, v___x_185_);
v___x_187_ = lean_array_uget_borrowed(v_buckets_172_, v___x_186_);
v___x_188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_171_, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg___boxed(lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v_m_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_m_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(lean_object* v___x_194_, lean_object* v_as_195_, size_t v_sz_196_, size_t v_i_197_, lean_object* v_b_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_a_208_; uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_197_, v_sz_196_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_b_198_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lean_box(0);
v_a_215_ = lean_array_uget_borrowed(v_as_195_, v_i_197_);
v___x_216_ = l_Lean_TSyntax_getId(v_a_215_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_194_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_239_; 
v_val_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_239_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_239_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_239_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; 
lean_inc(v___x_216_);
v___x_222_ = l_Lean_Meta_getFVarFromUserName(v___x_216_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_222_);
v___x_224_ = l_Lean_Expr_fvarId_x21(v_a_223_);
lean_dec(v_a_223_);
v___x_225_ = l_Lean_instBEqFVarId_beq(v___x_224_, v_val_218_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_216_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v_val_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 11);
lean_ctor_set(v___x_220_, 0, v___x_226_);
v___x_228_ = v___x_220_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v___x_228_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_dec_ref(v___x_229_);
v_a_208_ = v___x_214_;
goto v___jp_207_;
}
else
{
return v___x_229_;
}
}
}
else
{
lean_dec(v___x_224_);
lean_del_object(v___x_220_);
lean_dec(v_val_218_);
lean_dec(v___x_216_);
v_a_208_ = v___x_214_;
goto v___jp_207_;
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_del_object(v___x_220_);
lean_dec(v_val_218_);
lean_dec(v___x_216_);
v_a_231_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_222_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_222_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_dec(v___x_217_);
lean_dec(v___x_216_);
v_a_208_ = v___x_214_;
goto v___jp_207_;
}
}
v___jp_207_:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_197_, v___x_209_);
v_i_197_ = v___x_210_;
v_b_198_ = v_a_208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2___boxed(lean_object* v___x_240_, lean_object* v_as_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_b_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
size_t v_sz_boxed_253_; size_t v_i_boxed_254_; lean_object* v_res_255_; 
v_sz_boxed_253_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_254_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(v___x_240_, v_as_241_, v_sz_boxed_253_, v_i_boxed_254_, v_b_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec_ref(v_as_241_);
lean_dec_ref(v___x_240_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_256_, lean_object* v_vars_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
if (lean_obj_tag(v_letOrReassign_256_) == 2)
{
lean_object* v_mutVarDefs_266_; lean_object* v___x_267_; size_t v_sz_268_; size_t v___x_269_; lean_object* v___x_270_; 
v_mutVarDefs_266_ = lean_ctor_get(v_a_258_, 2);
v___x_267_ = lean_box(0);
v_sz_268_ = lean_array_size(v_vars_257_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__2(v_mutVarDefs_266_, v_vars_257_, v_sz_268_, v___x_269_, v___x_267_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_278_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_267_);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_267_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
return v___x_270_;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_281_, lean_object* v_vars_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_281_, v_vars_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_vars_282_);
lean_dec(v_letOrReassign_281_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_00_u03b2_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v_m_293_, v_a_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_00_u03b2_296_, lean_object* v_m_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_00_u03b2_296_, v_m_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_m_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2(lean_object* v_t_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___redArg(v_t_300_, v___y_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2___boxed(lean_object* v_t_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1_spec__2(v_t_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(lean_object* v_00_u03b2_320_, lean_object* v_a_321_, lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_a_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_324_, lean_object* v_a_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(v_00_u03b2_324_, v_a_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(lean_object* v_elabBody_328_, lean_object* v_body_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
lean_inc(v___y_332_);
lean_inc_ref(v___y_331_);
v___x_338_ = lean_apply_8(v_elabBody_328_, v_body_329_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, lean_box(0));
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object* v_elabBody_339_, lean_object* v_body_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(v_elabBody_339_, v_body_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(lean_object* v_letOrReassign_350_, lean_object* v_vars_351_, lean_object* v_k_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_350_, v_vars_351_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_361_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc_ref(v___y_353_);
v___x_362_ = lean_apply_8(v_k_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, lean_box(0));
return v___x_362_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_k_352_);
v_a_363_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_361_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed(lean_object* v_letOrReassign_371_, lean_object* v_vars_372_, lean_object* v_k_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(v_letOrReassign_371_, v_vars_372_, v_k_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec_ref(v_vars_372_);
lean_dec(v_letOrReassign_371_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith(lean_object* v_hint_383_, lean_object* v_letOrReassign_384_, lean_object* v_vars_385_, lean_object* v_k_386_, lean_object* v_elabBody_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v_elabCont_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed), 10, 1);
lean_closure_set(v___f_396_, 0, v_elabBody_387_);
lean_inc_ref(v_vars_385_);
lean_inc(v_letOrReassign_384_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_397_, 0, v_letOrReassign_384_);
lean_closure_set(v___f_397_, 1, v_vars_385_);
lean_closure_set(v___f_397_, 2, v_k_386_);
v___x_398_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_384_);
lean_dec(v_letOrReassign_384_);
v_elabCont_399_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVars_x3f___boxed), 12, 4);
lean_closure_set(v_elabCont_399_, 0, lean_box(0));
lean_closure_set(v_elabCont_399_, 1, v___x_398_);
lean_closure_set(v_elabCont_399_, 2, v_vars_385_);
lean_closure_set(v_elabCont_399_, 3, v___f_397_);
v___x_400_ = lean_box(0);
v___x_401_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v_hint_383_, v_elabCont_399_, v___f_396_, v___x_400_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___boxed(lean_object* v_hint_402_, lean_object* v_letOrReassign_403_, lean_object* v_vars_404_, lean_object* v_k_405_, lean_object* v_elabBody_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Do_elabDoLetOrReassignWith(v_hint_402_, v_letOrReassign_403_, v_vars_404_, v_k_405_, v_elabBody_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_416_, lean_object* v_vars_417_, lean_object* v_k_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc_ref(v_vars_417_);
lean_inc(v_letOrReassign_416_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_427_, 0, v_letOrReassign_416_);
lean_closure_set(v___f_427_, 1, v_vars_417_);
lean_closure_set(v___f_427_, 2, v_k_418_);
v___x_428_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_416_);
lean_dec(v_letOrReassign_416_);
v___x_429_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_428_, v_vars_417_, v___f_427_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_430_, lean_object* v_vars_431_, lean_object* v_k_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_430_, v_vars_431_, v_k_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_460_, lean_object* v_a_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_470_, lean_object* v_a_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_470_, v_a_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; lean_object* v_env_487_; lean_object* v___x_488_; lean_object* v_mctx_489_; lean_object* v_lctx_490_; lean_object* v_options_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_486_ = lean_st_ref_get(v___y_484_);
v_env_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc_ref(v_env_487_);
lean_dec(v___x_486_);
v___x_488_ = lean_st_ref_get(v___y_482_);
v_mctx_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc_ref(v_mctx_489_);
lean_dec(v___x_488_);
v_lctx_490_ = lean_ctor_get(v___y_481_, 2);
v_options_491_ = lean_ctor_get(v___y_483_, 2);
lean_inc_ref(v_options_491_);
lean_inc_ref(v_lctx_490_);
v___x_492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_492_, 0, v_env_487_);
lean_ctor_set(v___x_492_, 1, v_mctx_489_);
lean_ctor_set(v___x_492_, 2, v_lctx_490_);
lean_ctor_set(v___x_492_, 3, v_options_491_);
v___x_493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_msgData_480_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(1);
v___x_503_ = l_Lean_MessageData_ofFormat(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2));
v___x_508_ = l_Lean_MessageData_ofFormat(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_509_;
}
else
{
lean_object* v_head_511_; lean_object* v_tail_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_534_; 
v_head_511_ = lean_ctor_get(v_x_510_, 0);
v_tail_512_ = lean_ctor_get(v_x_510_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_534_ == 0)
{
v___x_514_ = v_x_510_;
v_isShared_515_ = v_isSharedCheck_534_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tail_512_);
lean_inc(v_head_511_);
lean_dec(v_x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_534_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_before_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_532_; 
v_before_516_ = lean_ctor_get(v_head_511_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_head_511_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_head_511_, 1);
lean_dec(v_unused_533_);
v___x_518_ = v_head_511_;
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_before_516_);
lean_dec(v_head_511_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 7);
lean_ctor_set(v___x_518_, 1, v___x_520_);
lean_ctor_set(v___x_518_, 0, v_x_509_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_x_509_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_531_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 7);
lean_ctor_set(v___x_514_, 1, v___x_523_);
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_525_ = v___x_514_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_523_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_MessageData_ofSyntax(v_before_516_);
v___x_527_ = l_Lean_indentD(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v_x_509_ = v___x_528_;
v_x_510_ = v_tail_512_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object* v_opts_535_, lean_object* v_opt_536_){
_start:
{
lean_object* v_name_537_; lean_object* v_defValue_538_; lean_object* v_map_539_; lean_object* v___x_540_; 
v_name_537_ = lean_ctor_get(v_opt_536_, 0);
v_defValue_538_ = lean_ctor_get(v_opt_536_, 1);
v_map_539_ = lean_ctor_get(v_opts_535_, 0);
v___x_540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_539_, v_name_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_unbox(v_defValue_538_);
return v___x_541_;
}
else
{
lean_object* v_val_542_; 
v_val_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_542_);
lean_dec_ref(v___x_540_);
if (lean_obj_tag(v_val_542_) == 1)
{
uint8_t v_v_543_; 
v_v_543_ = lean_ctor_get_uint8(v_val_542_, 0);
lean_dec_ref(v_val_542_);
return v_v_543_;
}
else
{
uint8_t v___x_544_; 
lean_dec(v_val_542_);
v___x_544_ = lean_unbox(v_defValue_538_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_545_, lean_object* v_opt_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_opts_545_, v_opt_546_);
lean_dec_ref(v_opt_546_);
lean_dec_ref(v_opts_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1));
v___x_553_ = l_Lean_MessageData_ofFormat(v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object* v_msgData_554_, lean_object* v_macroStack_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_options_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_options_558_ = lean_ctor_get(v___y_556_, 2);
v___x_559_ = l_Lean_Elab_pp_macroStack;
v___x_560_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec(v_macroStack_555_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_msgData_554_);
return v___x_561_;
}
else
{
if (lean_obj_tag(v_macroStack_555_) == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_msgData_554_);
return v___x_562_;
}
else
{
lean_object* v_head_563_; lean_object* v_after_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_579_; 
v_head_563_ = lean_ctor_get(v_macroStack_555_, 0);
lean_inc(v_head_563_);
v_after_564_ = lean_ctor_get(v_head_563_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_head_563_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_head_563_, 0);
lean_dec(v_unused_580_);
v___x_566_ = v_head_563_;
v_isShared_567_ = v_isSharedCheck_579_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_after_564_);
lean_dec(v_head_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_579_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 7);
lean_ctor_set(v___x_566_, 1, v___x_568_);
lean_ctor_set(v___x_566_, 0, v_msgData_554_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_msgData_554_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_578_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_msgData_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_MessageData_ofSyntax(v_after_564_);
v___x_574_ = l_Lean_indentD(v___x_573_);
v_msgData_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_575_, 0, v___x_572_);
lean_ctor_set(v_msgData_575_, 1, v___x_574_);
v___x_576_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(v_msgData_575_, v_macroStack_555_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_581_, lean_object* v_macroStack_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_581_, v_macroStack_582_, v___y_583_);
lean_dec_ref(v___y_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_ref_594_; lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v_macroStack_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_ref_594_ = lean_ctor_get(v___y_591_, 5);
v___x_595_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_586_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_595_);
v_macroStack_597_ = lean_ctor_get(v___y_587_, 1);
v___x_598_ = l_Lean_Elab_getBetterRef(v_ref_594_, v_macroStack_597_);
lean_inc(v_macroStack_597_);
v___x_599_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_596_, v_macroStack_597_, v___y_591_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_598_);
lean_ctor_set(v___x_604_, 1, v_a_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 1);
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Array_mkArray0(lean_box(0));
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_665_ = l_String_toRawSubstring_x27(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_712_, lean_object* v_decl_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
if (lean_obj_tag(v_letOrReassign_712_) == 2)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_713_);
v___x_722_ = l_Lean_Syntax_isOfKind(v_decl_713_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_724_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_725_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_Syntax_getArg(v_decl_713_, v___x_727_);
v___x_729_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_728_);
v___x_730_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___y_733_; lean_object* v_pattern_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___x_803_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_728_);
v___x_803_ = l_Lean_Syntax_isOfKind(v___x_728_, v___x_731_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v___x_728_);
v___x_804_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_805_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_806_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = l_Lean_Syntax_getArg(v___x_728_, v___x_808_);
v___x_810_ = l_Lean_Syntax_matchesNull(v___x_809_, v___x_727_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v___x_728_);
v___x_811_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_812_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_813_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_814_;
}
else
{
lean_object* v_pattern_815_; lean_object* v_xType_x3f_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_pattern_815_ = l_Lean_Syntax_getArg(v___x_728_, v___x_727_);
v___x_850_ = lean_unsigned_to_nat(2u);
v___x_851_ = l_Lean_Syntax_getArg(v___x_728_, v___x_850_);
v___x_852_ = l_Lean_Syntax_isNone(v___x_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; 
lean_inc(v___x_851_);
v___x_853_ = l_Lean_Syntax_matchesNull(v___x_851_, v___x_808_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v___x_851_);
lean_dec(v_pattern_815_);
lean_dec(v___x_728_);
v___x_854_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_855_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_856_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = l_Lean_Syntax_getArg(v___x_851_, v___x_727_);
lean_dec(v___x_851_);
v___x_859_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_858_);
v___x_860_ = l_Lean_Syntax_isOfKind(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec(v___x_858_);
lean_dec(v_pattern_815_);
lean_dec(v___x_728_);
v___x_861_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_862_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_863_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_864_;
}
else
{
lean_object* v_xType_x3f_865_; lean_object* v___x_866_; 
lean_dec(v_decl_713_);
v_xType_x3f_865_ = l_Lean_Syntax_getArg(v___x_858_, v___x_808_);
lean_dec(v___x_858_);
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_xType_x3f_865_);
v_xType_x3f_817_ = v___x_866_;
v___y_818_ = v_a_714_;
v___y_819_ = v_a_715_;
v___y_820_ = v_a_716_;
v___y_821_ = v_a_717_;
v___y_822_ = v_a_718_;
v___y_823_ = v_a_719_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v___x_867_; 
lean_dec(v___x_851_);
lean_dec(v_decl_713_);
v___x_867_ = lean_box(0);
v_xType_x3f_817_ = v___x_867_;
v___y_818_ = v_a_714_;
v___y_819_ = v_a_715_;
v___y_820_ = v_a_716_;
v___y_821_ = v_a_717_;
v___y_822_ = v_a_718_;
v___y_823_ = v_a_719_;
goto v___jp_816_;
}
v___jp_816_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(4u);
v___x_825_ = l_Lean_Syntax_getArg(v___x_728_, v___x_824_);
lean_dec(v___x_728_);
if (lean_obj_tag(v_xType_x3f_817_) == 0)
{
v___y_733_ = v___x_825_;
v_pattern_734_ = v_pattern_815_;
v___y_735_ = v___y_818_;
v___y_736_ = v___y_819_;
v___y_737_ = v___y_820_;
v___y_738_ = v___y_821_;
v___y_739_ = v___y_822_;
v___y_740_ = v___y_823_;
goto v___jp_732_;
}
else
{
lean_object* v_val_826_; lean_object* v_ref_827_; lean_object* v_quotContext_828_; lean_object* v_currMacroScope_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_val_826_ = lean_ctor_get(v_xType_x3f_817_, 0);
lean_inc(v_val_826_);
lean_dec_ref(v_xType_x3f_817_);
v_ref_827_ = lean_ctor_get(v___y_822_, 5);
v_quotContext_828_ = lean_ctor_get(v___y_822_, 10);
v_currMacroScope_829_ = lean_ctor_get(v___y_822_, 11);
v___x_830_ = l_Lean_SourceInfo_fromRef(v_ref_827_, v___x_730_);
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_830_, 7);
v___x_834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_830_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_836_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_837_ = lean_box(0);
lean_inc(v_currMacroScope_829_);
lean_inc(v_quotContext_828_);
v___x_838_ = l_Lean_addMacroScope(v_quotContext_828_, v___x_837_, v_currMacroScope_829_);
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_840_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_840_, 0, v___x_830_);
lean_ctor_set(v___x_840_, 1, v___x_836_);
lean_ctor_set(v___x_840_, 2, v___x_838_);
lean_ctor_set(v___x_840_, 3, v___x_839_);
v___x_841_ = l_Lean_Syntax_node1(v___x_830_, v___x_835_, v___x_840_);
v___x_842_ = l_Lean_Syntax_node2(v___x_830_, v___x_832_, v___x_834_, v___x_841_);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_830_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_846_ = l_Lean_Syntax_node1(v___x_830_, v___x_845_, v_val_826_);
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_830_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_Syntax_node5(v___x_830_, v___x_831_, v___x_842_, v_pattern_815_, v___x_844_, v___x_846_, v___x_848_);
v___y_733_ = v___x_825_;
v_pattern_734_ = v___x_849_;
v___y_735_ = v___y_818_;
v___y_736_ = v___y_819_;
v___y_737_ = v___y_820_;
v___y_738_ = v___y_821_;
v___y_739_ = v___y_822_;
v___y_740_ = v___y_823_;
goto v___jp_732_;
}
}
}
}
v___jp_732_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = lean_box(0);
v___x_742_ = lean_box(v___x_722_);
v___x_743_ = lean_box(v___x_722_);
lean_inc(v_pattern_734_);
v___x_744_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_744_, 0, v_pattern_734_);
lean_closure_set(v___x_744_, 1, v___x_741_);
lean_closure_set(v___x_744_, 2, v___x_742_);
lean_closure_set(v___x_744_, 3, v___x_743_);
v___x_745_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_744_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_745_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
v___x_747_ = lean_infer_type(v_a_746_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v___x_749_ = l_Lean_Elab_Term_exprToSyntax(v_a_748_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_786_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_786_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_786_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_786_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_ref_754_; lean_object* v_quotContext_755_; lean_object* v_currMacroScope_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v_ref_754_ = lean_ctor_get(v___y_739_, 5);
v_quotContext_755_ = lean_ctor_get(v___y_739_, 10);
v_currMacroScope_756_ = lean_ctor_get(v___y_739_, 11);
v___x_757_ = l_Lean_SourceInfo_fromRef(v_ref_754_, v___x_730_);
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_759_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_757_, 11);
v___x_760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_758_);
lean_ctor_set(v___x_760_, 2, v___x_759_);
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_757_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_765_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_757_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_768_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_769_ = lean_box(0);
lean_inc(v_currMacroScope_756_);
lean_inc(v_quotContext_755_);
v___x_770_ = l_Lean_addMacroScope(v_quotContext_755_, v___x_769_, v_currMacroScope_756_);
v___x_771_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_772_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_772_, 0, v___x_757_);
lean_ctor_set(v___x_772_, 1, v___x_768_);
lean_ctor_set(v___x_772_, 2, v___x_770_);
lean_ctor_set(v___x_772_, 3, v___x_771_);
v___x_773_ = l_Lean_Syntax_node1(v___x_757_, v___x_767_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___x_757_, v___x_764_, v___x_766_, v___x_773_);
v___x_775_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_757_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_757_, v___x_758_, v_a_750_);
v___x_778_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_757_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_Syntax_node5(v___x_757_, v___x_763_, v___x_774_, v___y_733_, v___x_776_, v___x_777_, v___x_779_);
lean_inc_ref(v___x_760_);
v___x_781_ = l_Lean_Syntax_node5(v___x_757_, v___x_731_, v_pattern_734_, v___x_760_, v___x_760_, v___x_762_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node1(v___x_757_, v___x_721_, v___x_781_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_782_);
v___x_784_ = v___x_752_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_dec(v_pattern_734_);
lean_dec(v___y_733_);
return v___x_749_;
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_pattern_734_);
lean_dec(v___y_733_);
v_a_787_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_747_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_747_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_pattern_734_);
lean_dec(v___y_733_);
v_a_795_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_745_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_745_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_868_ = l_Lean_Syntax_getArg(v___x_728_, v___x_727_);
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_868_);
v___x_870_ = l_Lean_Syntax_isOfKind(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v___x_868_);
lean_dec(v___x_728_);
v___x_871_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_872_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_873_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_874_;
}
else
{
lean_object* v_x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v_a_884_; lean_object* v_xType_x3f_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_x_875_ = l_Lean_Syntax_getArg(v___x_868_, v___x_727_);
lean_dec(v___x_868_);
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_875_);
v___x_962_ = l_Lean_Syntax_isOfKind(v_x_875_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_x_875_);
lean_dec(v___x_728_);
v___x_963_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_964_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_965_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = l_Lean_Syntax_getArg(v___x_728_, v___x_967_);
v___x_969_ = l_Lean_Syntax_matchesNull(v___x_968_, v___x_727_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_x_875_);
lean_dec(v___x_728_);
v___x_970_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_971_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_972_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(2u);
v___x_975_ = l_Lean_Syntax_getArg(v___x_728_, v___x_974_);
v___x_976_ = l_Lean_Syntax_isNone(v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; 
lean_inc(v___x_975_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_975_, v___x_967_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v___x_975_);
lean_dec(v_x_875_);
lean_dec(v___x_728_);
v___x_978_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_979_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_980_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = l_Lean_Syntax_getArg(v___x_975_, v___x_727_);
lean_dec(v___x_975_);
v___x_983_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_982_);
v___x_984_ = l_Lean_Syntax_isOfKind(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v___x_982_);
lean_dec(v_x_875_);
lean_dec(v___x_728_);
v___x_985_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_986_ = l_Lean_MessageData_ofSyntax(v_decl_713_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_987_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
return v___x_988_;
}
else
{
lean_object* v_xType_x3f_989_; lean_object* v___x_990_; 
lean_dec(v_decl_713_);
v_xType_x3f_989_ = l_Lean_Syntax_getArg(v___x_982_, v___x_967_);
lean_dec(v___x_982_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_xType_x3f_989_);
v_xType_x3f_933_ = v___x_990_;
v___y_934_ = v_a_714_;
v___y_935_ = v_a_715_;
v___y_936_ = v_a_716_;
v___y_937_ = v_a_717_;
v___y_938_ = v_a_718_;
v___y_939_ = v_a_719_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v___x_991_; 
lean_dec(v___x_975_);
lean_dec(v_decl_713_);
v___x_991_ = lean_box(0);
v_xType_x3f_933_ = v___x_991_;
v___y_934_ = v_a_714_;
v___y_935_ = v_a_715_;
v___y_936_ = v_a_716_;
v___y_937_ = v_a_717_;
v___y_938_ = v_a_718_;
v___y_939_ = v_a_719_;
goto v___jp_932_;
}
}
}
v___jp_876_:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_box(0);
lean_inc(v_x_875_);
v___x_886_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_875_, v_a_884_, v___x_722_, v___x_722_, v___x_885_, v___y_879_, v___y_880_, v___y_883_, v___y_881_, v___y_877_, v___y_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v___x_886_);
v___x_887_ = l_Lean_TSyntax_getId(v_x_875_);
v___x_888_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_887_, v___y_883_, v___y_881_, v___y_877_, v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = l_Lean_LocalDecl_type(v_a_889_);
lean_dec(v_a_889_);
v___x_891_ = l_Lean_Elab_Term_exprToSyntax(v___x_890_, v___y_879_, v___y_880_, v___y_883_, v___y_881_, v___y_877_, v___y_882_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_915_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_915_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_915_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_915_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_ref_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v_ref_896_ = lean_ctor_get(v___y_877_, 5);
v___x_897_ = 0;
v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_896_, v___x_897_);
lean_inc_n(v___x_898_, 7);
v___x_899_ = l_Lean_Syntax_node1(v___x_898_, v___x_869_, v_x_875_);
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_901_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_898_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_Syntax_node2(v___x_898_, v___x_903_, v___x_905_, v_a_892_);
v___x_907_ = l_Lean_Syntax_node1(v___x_898_, v___x_900_, v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_898_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_Syntax_node5(v___x_898_, v___x_729_, v___x_899_, v___x_902_, v___x_907_, v___x_909_, v___y_878_);
v___x_911_ = l_Lean_Syntax_node1(v___x_898_, v___x_721_, v___x_910_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_911_);
v___x_913_ = v___x_894_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
lean_dec(v___y_878_);
lean_dec(v_x_875_);
return v___x_891_;
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v___y_878_);
lean_dec(v_x_875_);
v_a_916_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_888_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_888_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v___y_878_);
lean_dec(v_x_875_);
v_a_924_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_886_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_886_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
v___jp_932_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(4u);
v___x_941_ = l_Lean_Syntax_getArg(v___x_728_, v___x_940_);
lean_dec(v___x_728_);
if (lean_obj_tag(v_xType_x3f_933_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_box(0);
v___y_877_ = v___y_938_;
v___y_878_ = v___x_941_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_935_;
v___y_881_ = v___y_937_;
v___y_882_ = v___y_939_;
v___y_883_ = v___y_936_;
v_a_884_ = v___x_942_;
goto v___jp_876_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_960_; 
v_val_943_ = lean_ctor_get(v_xType_x3f_933_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_xType_x3f_933_);
if (v_isSharedCheck_960_ == 0)
{
v___x_945_ = v_xType_x3f_933_;
v_isShared_946_ = v_isSharedCheck_960_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v_xType_x3f_933_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_960_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Elab_Term_elabType(v_val_943_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v___x_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_a_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v___y_877_ = v___y_938_;
v___y_878_ = v___x_941_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_935_;
v___y_881_ = v___y_937_;
v___y_882_ = v___y_939_;
v___y_883_ = v___y_936_;
v_a_884_ = v___x_950_;
goto v___jp_876_;
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_945_);
lean_dec(v___x_941_);
lean_dec(v_x_875_);
v_a_952_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_947_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
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
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_decl_713_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_993_, lean_object* v_decl_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_993_, v_decl_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_letOrReassign_993_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_1013_, v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_1023_, lean_object* v_macroStack_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_1023_, v_macroStack_1024_, v___y_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_1033_, lean_object* v_macroStack_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_1033_, v_macroStack_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_ref_1049_; lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_ref_1049_ = lean_ctor_get(v___y_1046_, 5);
v___x_1050_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc(v_ref_1049_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_ref_1049_);
lean_ctor_set(v___x_1055_, 1, v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_postponeValue_1082_; uint8_t v_generalize_1083_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; 
v_postponeValue_1082_ = lean_ctor_get_uint8(v_config_1073_, sizeof(void*)*1 + 3);
v_generalize_1083_ = lean_ctor_get_uint8(v_config_1073_, sizeof(void*)*1 + 4);
if (v_postponeValue_1082_ == 0)
{
v___y_1085_ = v_a_1074_;
v___y_1086_ = v_a_1075_;
v___y_1087_ = v_a_1076_;
v___y_1088_ = v_a_1077_;
v___y_1089_ = v_a_1078_;
v___y_1090_ = v_a_1079_;
v___y_1091_ = v_a_1080_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_1097_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1096_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
return v___x_1097_;
}
v___jp_1084_:
{
if (v_generalize_1083_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_1095_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1094_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec_ref(v_config_1098_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1109_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_msg_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_1119_, v_msg_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_keyedConfig_1167_; uint8_t v_trackZetaDelta_1168_; lean_object* v_zetaDeltaSet_1169_; lean_object* v_localInstances_1170_; lean_object* v_defEqCtx_x3f_1171_; lean_object* v_synthPendingDepth_1172_; lean_object* v_canUnfold_x3f_1173_; uint8_t v_univApprox_1174_; uint8_t v_inTypeClassResolution_1175_; uint8_t v_cacheInferType_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_keyedConfig_1167_ = lean_ctor_get(v___y_1162_, 0);
v_trackZetaDelta_1168_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*7);
v_zetaDeltaSet_1169_ = lean_ctor_get(v___y_1162_, 1);
v_localInstances_1170_ = lean_ctor_get(v___y_1162_, 3);
v_defEqCtx_x3f_1171_ = lean_ctor_get(v___y_1162_, 4);
v_synthPendingDepth_1172_ = lean_ctor_get(v___y_1162_, 5);
v_canUnfold_x3f_1173_ = lean_ctor_get(v___y_1162_, 6);
v_univApprox_1174_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1175_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*7 + 2);
v_cacheInferType_1176_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1173_);
lean_inc(v_synthPendingDepth_1172_);
lean_inc(v_defEqCtx_x3f_1171_);
lean_inc_ref(v_localInstances_1170_);
lean_inc(v_zetaDeltaSet_1169_);
lean_inc_ref(v_keyedConfig_1167_);
v___x_1177_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1177_, 0, v_keyedConfig_1167_);
lean_ctor_set(v___x_1177_, 1, v_zetaDeltaSet_1169_);
lean_ctor_set(v___x_1177_, 2, v_lctx_1158_);
lean_ctor_set(v___x_1177_, 3, v_localInstances_1170_);
lean_ctor_set(v___x_1177_, 4, v_defEqCtx_x3f_1171_);
lean_ctor_set(v___x_1177_, 5, v_synthPendingDepth_1172_);
lean_ctor_set(v___x_1177_, 6, v_canUnfold_x3f_1173_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*7, v_trackZetaDelta_1168_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*7 + 1, v_univApprox_1174_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1175_);
lean_ctor_set_uint8(v___x_1177_, sizeof(void*)*7 + 3, v_cacheInferType_1176_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
v___x_1178_ = lean_apply_7(v_x_1159_, v___y_1160_, v___y_1161_, v___x_1177_, v___y_1163_, v___y_1164_, v___y_1165_, lean_box(0));
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1197_, lean_object* v_lctx_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1198_, v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_lctx_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1208_, v_lctx_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1229_ = lean_apply_9(v_k_1219_, v_b_1223_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v_b_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1241_, lean_object* v_type_1242_, lean_object* v_val_1243_, lean_object* v_k_1244_, uint8_t v_nondep_1245_, uint8_t v_kind_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___f_1255_; lean_object* v___x_1256_; 
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc_ref(v___y_1247_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1255_, 0, v_k_1244_);
lean_closure_set(v___f_1255_, 1, v___y_1247_);
lean_closure_set(v___f_1255_, 2, v___y_1248_);
lean_closure_set(v___f_1255_, 3, v___y_1249_);
v___x_1256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1241_, v_type_1242_, v_val_1243_, v___f_1255_, v_nondep_1245_, v_kind_1246_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
return v___x_1256_;
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1265_, lean_object* v_type_1266_, lean_object* v_val_1267_, lean_object* v_k_1268_, lean_object* v_nondep_1269_, lean_object* v_kind_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_nondep_boxed_1279_; uint8_t v_kind_boxed_1280_; lean_object* v_res_1281_; 
v_nondep_boxed_1279_ = lean_unbox(v_nondep_1269_);
v_kind_boxed_1280_ = lean_unbox(v_kind_1270_);
v_res_1281_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1265_, v_type_1266_, v_val_1267_, v_k_1268_, v_nondep_boxed_1279_, v_kind_boxed_1280_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1282_, lean_object* v_name_1283_, lean_object* v_type_1284_, lean_object* v_val_1285_, lean_object* v_k_1286_, uint8_t v_nondep_1287_, uint8_t v_kind_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1283_, v_type_1284_, v_val_1285_, v_k_1286_, v_nondep_1287_, v_kind_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_name_1299_, lean_object* v_type_1300_, lean_object* v_val_1301_, lean_object* v_k_1302_, lean_object* v_nondep_1303_, lean_object* v_kind_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_nondep_boxed_1313_; uint8_t v_kind_boxed_1314_; lean_object* v_res_1315_; 
v_nondep_boxed_1313_ = lean_unbox(v_nondep_1303_);
v_kind_boxed_1314_ = lean_unbox(v_kind_1304_);
v_res_1315_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1298_, v_name_1299_, v_type_1300_, v_val_1301_, v_k_1302_, v_nondep_boxed_1313_, v_kind_boxed_1314_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1316_, lean_object* v___x_1317_, uint8_t v___x_1318_, lean_object* v___x_1319_, lean_object* v___x_1320_, uint8_t v___x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1316_, v___x_1317_, v___x_1318_, v___x_1318_, v___x_1319_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = 1;
v___x_1332_ = l_Lean_Meta_mkLambdaFVars(v___x_1320_, v_a_1330_, v___x_1321_, v___x_1321_, v___x_1321_, v___x_1318_, v___x_1331_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1332_;
}
else
{
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v___x_98796__boxed_1346_; uint8_t v___x_98799__boxed_1347_; lean_object* v_res_1348_; 
v___x_98796__boxed_1346_ = lean_unbox(v___x_1335_);
v___x_98799__boxed_1347_ = lean_unbox(v___x_1338_);
v_res_1348_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1333_, v___x_1334_, v___x_98796__boxed_1346_, v___x_1336_, v___x_1337_, v___x_98799__boxed_1347_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v___x_1337_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_ks_1353_; lean_object* v_vs_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1378_; 
v_ks_1353_ = lean_ctor_get(v_x_1349_, 0);
v_vs_1354_ = lean_ctor_get(v_x_1349_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1356_ = v_x_1349_;
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_vs_1354_);
lean_inc(v_ks_1353_);
lean_dec(v_x_1349_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_array_get_size(v_ks_1353_);
v___x_1359_ = lean_nat_dec_lt(v_x_1350_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_x_1350_);
v___x_1360_ = lean_array_push(v_ks_1353_, v_x_1351_);
v___x_1361_ = lean_array_push(v_vs_1354_, v_x_1352_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1361_);
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v_k_x27_1365_; uint8_t v___x_1366_; 
v_k_x27_1365_ = lean_array_fget_borrowed(v_ks_1353_, v_x_1350_);
v___x_1366_ = l_Lean_instBEqFVarId_beq(v_x_1351_, v_k_x27_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1368_; 
if (v_isShared_1357_ == 0)
{
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_ks_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_vs_1354_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_x_1350_, v___x_1369_);
lean_dec(v_x_1350_);
v_x_1349_ = v___x_1368_;
v_x_1350_ = v___x_1370_;
goto _start;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1373_ = lean_array_fset(v_ks_1353_, v_x_1350_, v_x_1351_);
v___x_1374_ = lean_array_fset(v_vs_1354_, v_x_1350_, v_x_1352_);
lean_dec(v_x_1350_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1374_);
lean_ctor_set(v___x_1356_, 0, v___x_1373_);
v___x_1376_ = v___x_1356_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1379_, lean_object* v_k_1380_, lean_object* v_v_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1379_, v___x_1382_, v_k_1380_, v_v_1381_);
return v___x_1383_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; 
v___x_1384_ = ((size_t)5ULL);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_shift_left(v___x_1385_, v___x_1384_);
return v___x_1386_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; 
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1389_ = lean_usize_sub(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1391_, size_t v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_es_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v_j_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_es_1396_ = lean_ctor_get(v_x_1391_, 0);
v___x_1397_ = ((size_t)5ULL);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_1400_ = lean_usize_land(v_x_1392_, v___x_1399_);
v_j_1401_ = lean_usize_to_nat(v___x_1400_);
v___x_1402_ = lean_array_get_size(v_es_1396_);
v___x_1403_ = lean_nat_dec_lt(v_j_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec(v_j_1401_);
lean_dec(v_x_1395_);
lean_dec(v_x_1394_);
return v_x_1391_;
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1440_; 
lean_inc_ref(v_es_1396_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_x_1391_, 0);
lean_dec(v_unused_1441_);
v___x_1405_ = v_x_1391_;
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_xs_x27_1409_; lean_object* v___y_1411_; 
v_v_1407_ = lean_array_fget(v_es_1396_, v_j_1401_);
v___x_1408_ = lean_box(0);
v_xs_x27_1409_ = lean_array_fset(v_es_1396_, v_j_1401_, v___x_1408_);
switch(lean_obj_tag(v_v_1407_))
{
case 0:
{
lean_object* v_key_1416_; lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1427_; 
v_key_1416_ = lean_ctor_get(v_v_1407_, 0);
v_val_1417_ = lean_ctor_get(v_v_1407_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1419_ = v_v_1407_;
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_inc(v_key_1416_);
lean_dec(v_v_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = l_Lean_instBEqFVarId_beq(v_x_1394_, v_key_1416_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1419_);
v___x_1422_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1416_, v_val_1417_, v_x_1394_, v_x_1395_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___y_1411_ = v___x_1423_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_val_1417_);
lean_dec(v_key_1416_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_x_1395_);
lean_ctor_set(v___x_1419_, 0, v_x_1394_);
v___x_1425_ = v___x_1419_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_x_1394_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_x_1395_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v___y_1411_ = v___x_1425_;
goto v___jp_1410_;
}
}
}
}
case 1:
{
lean_object* v_node_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_node_1428_ = lean_ctor_get(v_v_1407_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_v_1407_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_node_1428_);
lean_dec(v_v_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_usize_shift_right(v_x_1392_, v___x_1397_);
v___x_1433_ = lean_usize_add(v_x_1393_, v___x_1398_);
v___x_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1428_, v___x_1432_, v___x_1433_, v_x_1394_, v_x_1395_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1411_ = v___x_1436_;
goto v___jp_1410_;
}
}
}
default: 
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_x_1394_);
lean_ctor_set(v___x_1439_, 1, v_x_1395_);
v___y_1411_ = v___x_1439_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_array_fset(v_xs_x27_1409_, v_j_1401_, v___y_1411_);
lean_dec(v_j_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1412_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1463_; 
v_ks_1442_ = lean_ctor_get(v_x_1391_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1391_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1445_ = v_x_1391_;
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_vs_1443_);
lean_inc(v_ks_1442_);
lean_dec(v_x_1391_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_ks_1442_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_vs_1443_);
v___x_1448_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v_newNode_1449_; uint8_t v___y_1451_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_newNode_1449_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1448_, v_x_1394_, v_x_1395_);
v___x_1457_ = ((size_t)7ULL);
v___x_1458_ = lean_usize_dec_le(v___x_1457_, v_x_1393_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1449_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
v___y_1451_ = v___x_1461_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___x_1458_;
goto v___jp_1450_;
}
v___jp_1450_:
{
if (v___y_1451_ == 0)
{
lean_object* v_ks_1452_; lean_object* v_vs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ks_1452_ = lean_ctor_get(v_newNode_1449_, 0);
lean_inc_ref(v_ks_1452_);
v_vs_1453_ = lean_ctor_get(v_newNode_1449_, 1);
lean_inc_ref(v_vs_1453_);
lean_dec_ref(v_newNode_1449_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__2);
v___x_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1393_, v_ks_1452_, v_vs_1453_, v___x_1454_, v___x_1455_);
lean_dec_ref(v_vs_1453_);
lean_dec_ref(v_ks_1452_);
return v___x_1456_;
}
else
{
return v_newNode_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_array_get_size(v_keys_1465_);
v___x_1470_ = lean_nat_dec_lt(v_i_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v_i_1467_);
return v_entries_1468_;
}
else
{
lean_object* v_k_1471_; lean_object* v_v_1472_; uint64_t v___x_1473_; size_t v_h_1474_; size_t v___x_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v_h_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_k_1471_ = lean_array_fget_borrowed(v_keys_1465_, v_i_1467_);
v_v_1472_ = lean_array_fget_borrowed(v_vals_1466_, v_i_1467_);
v___x_1473_ = l_Lean_instHashableFVarId_hash(v_k_1471_);
v_h_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = ((size_t)5ULL);
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_sub(v_depth_1464_, v___x_1477_);
v___x_1479_ = lean_usize_mul(v___x_1475_, v___x_1478_);
v_h_1480_ = lean_usize_shift_right(v_h_1474_, v___x_1479_);
v___x_1481_ = lean_nat_add(v_i_1467_, v___x_1476_);
lean_dec(v_i_1467_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v___x_1482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1468_, v_h_1480_, v_depth_1464_, v_k_1471_, v_v_1472_);
v_i_1467_ = v___x_1481_;
v_entries_1468_ = v___x_1482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_i_1487_, lean_object* v_entries_1488_){
_start:
{
size_t v_depth_boxed_1489_; lean_object* v_res_1490_; 
v_depth_boxed_1489_ = lean_unbox_usize(v_depth_1484_);
lean_dec(v_depth_1484_);
v_res_1490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1489_, v_keys_1485_, v_vals_1486_, v_i_1487_, v_entries_1488_);
lean_dec_ref(v_vals_1486_);
lean_dec_ref(v_keys_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
size_t v_x_98931__boxed_1496_; size_t v_x_98932__boxed_1497_; lean_object* v_res_1498_; 
v_x_98931__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_x_98932__boxed_1497_ = lean_unbox_usize(v_x_1493_);
lean_dec(v_x_1493_);
v_res_1498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1491_, v_x_98931__boxed_1496_, v_x_98932__boxed_1497_, v_x_1494_, v_x_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint64_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1502_ = l_Lean_instHashableFVarId_hash(v_x_1500_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1499_, v___x_1503_, v___x_1504_, v_x_1500_, v_x_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1506_, size_t v_i_1507_, size_t v_stop_1508_, lean_object* v_b_1509_){
_start:
{
lean_object* v___y_1511_; uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_eq(v_i_1507_, v_stop_1508_);
if (v___x_1515_ == 0)
{
lean_object* v_fvarIdToDecl_1516_; lean_object* v_decls_1517_; lean_object* v_auxDeclToFullName_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_fvarIdToDecl_1516_ = lean_ctor_get(v_b_1509_, 0);
v_decls_1517_ = lean_ctor_get(v_b_1509_, 1);
v_auxDeclToFullName_1518_ = lean_ctor_get(v_b_1509_, 2);
v___x_1519_ = lean_array_uget_borrowed(v_as_1506_, v_i_1507_);
v___x_1520_ = l_Lean_Expr_fvarId_x21(v___x_1519_);
lean_inc_ref(v_b_1509_);
v___x_1521_ = lean_local_ctx_find(v_b_1509_, v___x_1520_);
if (lean_obj_tag(v___x_1521_) == 0)
{
v___y_1511_ = v_b_1509_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1548_; 
lean_inc(v_auxDeclToFullName_1518_);
lean_inc_ref(v_decls_1517_);
lean_inc_ref(v_fvarIdToDecl_1516_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_b_1509_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; 
v_unused_1549_ = lean_ctor_get(v_b_1509_, 2);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_b_1509_, 1);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_b_1509_, 0);
lean_dec(v_unused_1551_);
v___x_1523_ = v_b_1509_;
v_isShared_1524_ = v_isSharedCheck_1548_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v_b_1509_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1548_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1547_; 
v_val_1525_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1527_ = v___x_1521_;
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v___x_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1543_; lean_object* v_fvarId_1546_; 
v___x_1529_ = l_Lean_LocalDecl_type(v_val_1525_);
v___x_1530_ = l_Lean_Expr_cleanupAnnotations(v___x_1529_);
v___x_1531_ = l_Lean_LocalDecl_setType(v_val_1525_, v___x_1530_);
v_fvarId_1546_ = lean_ctor_get(v___x_1531_, 1);
lean_inc(v_fvarId_1546_);
v___y_1543_ = v_fvarId_1546_;
goto v___jp_1542_;
v___jp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1531_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1531_);
v___x_1536_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = l_Lean_PersistentArray_set___redArg(v_decls_1517_, v___y_1534_, v___x_1536_);
lean_dec(v___y_1534_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1537_);
lean_ctor_set(v___x_1523_, 0, v___y_1533_);
v___x_1539_ = v___x_1523_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___y_1533_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_auxDeclToFullName_1518_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
v___y_1511_ = v___x_1539_;
goto v___jp_1510_;
}
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v_index_1545_; 
lean_inc_ref(v___x_1531_);
v___x_1544_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1516_, v___y_1543_, v___x_1531_);
v_index_1545_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_index_1545_);
v___y_1533_ = v___x_1544_;
v___y_1534_ = v_index_1545_;
goto v___jp_1532_;
}
}
}
}
}
else
{
return v_b_1509_;
}
v___jp_1510_:
{
size_t v___x_1512_; size_t v___x_1513_; 
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = lean_usize_add(v_i_1507_, v___x_1512_);
v_i_1507_ = v___x_1513_;
v_b_1509_ = v___y_1511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1552_, lean_object* v_i_1553_, lean_object* v_stop_1554_, lean_object* v_b_1555_){
_start:
{
size_t v_i_boxed_1556_; size_t v_stop_boxed_1557_; lean_object* v_res_1558_; 
v_i_boxed_1556_ = lean_unbox_usize(v_i_1553_);
lean_dec(v_i_1553_);
v_stop_boxed_1557_ = lean_unbox_usize(v_stop_1554_);
lean_dec(v_stop_1554_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1552_, v_i_boxed_1556_, v_stop_boxed_1557_, v_b_1555_);
lean_dec_ref(v_as_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1559_, size_t v_i_1560_, lean_object* v_bs_1561_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1560_, v_sz_1559_);
if (v___x_1562_ == 0)
{
return v_bs_1561_;
}
else
{
lean_object* v_v_1563_; lean_object* v_snd_1564_; lean_object* v___x_1565_; lean_object* v_bs_x27_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_v_1563_ = lean_array_uget_borrowed(v_bs_1561_, v_i_1560_);
v_snd_1564_ = lean_ctor_get(v_v_1563_, 1);
lean_inc(v_snd_1564_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v_bs_x27_1566_ = lean_array_uset(v_bs_1561_, v_i_1560_, v___x_1565_);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1560_, v___x_1567_);
v___x_1569_ = lean_array_uset(v_bs_x27_1566_, v_i_1560_, v_snd_1564_);
v_i_1560_ = v___x_1568_;
v_bs_1561_ = v___x_1569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1571_, lean_object* v_i_1572_, lean_object* v_bs_1573_){
_start:
{
size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1571_);
lean_dec(v_sz_1571_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1572_);
lean_dec(v_i_1572_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1574_, v_i_boxed_1575_, v_bs_1573_);
return v_res_1576_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1582_ = l_Lean_stringToMessageData(v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1588_, lean_object* v_value_1589_, uint8_t v___x_1590_, uint8_t v___x_1591_, lean_object* v___x_1592_, uint8_t v___y_1593_, lean_object* v_xs_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; 
lean_inc(v_type_1588_);
v___x_1602_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1602_, 0, v_type_1588_);
v___x_1603_ = 2;
v___x_1604_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1602_, v___x_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___y_1610_; lean_object* v___y_1646_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v_sz_1606_ = lean_array_size(v_xs_1594_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1606_, v___x_1607_, v_xs_1594_);
if (v___y_1593_ == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1646_ = v___x_1682_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1646_ = v___x_1683_;
goto v___jp_1645_;
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
lean_inc(v_a_1605_);
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1605_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_box(v___x_1590_);
v___x_1614_ = lean_box(v___x_1591_);
lean_inc_ref(v___x_1608_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1615_, 0, v_value_1589_);
lean_closure_set(v___f_1615_, 1, v___x_1611_);
lean_closure_set(v___f_1615_, 2, v___x_1613_);
lean_closure_set(v___f_1615_, 3, v___x_1612_);
lean_closure_set(v___f_1615_, 4, v___x_1608_);
lean_closure_set(v___f_1615_, 5, v___x_1614_);
v___x_1616_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1610_, v___f_1615_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = 1;
v___x_1619_ = l_Lean_Meta_mkForallFVars(v___x_1608_, v_a_1605_, v___x_1591_, v___x_1590_, v___x_1590_, v___x_1618_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec_ref(v___x_1608_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1620_);
lean_ctor_set(v___x_1624_, 1, v_a_1617_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1617_);
v_a_1629_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1619_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1619_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v___x_1608_);
lean_dec(v_a_1605_);
v_a_1637_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1616_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1616_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
v___jp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1647_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1646_);
v___x_1648_ = l_Lean_stringToMessageData(v___y_1646_);
lean_inc_ref(v___x_1648_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
lean_inc(v_type_1588_);
v___x_1652_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1605_, v_type_1588_, v___x_1651_, v___y_1596_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v___x_1652_);
v___x_1653_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1648_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1650_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_inc(v_a_1605_);
v___x_1657_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1605_, v_type_1588_, v___x_1656_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_lctx_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_dec_ref(v___x_1657_);
v_lctx_1658_ = lean_ctor_get(v___y_1597_, 2);
v___x_1659_ = lean_array_get_size(v___x_1608_);
v___x_1660_ = lean_nat_dec_lt(v___x_1592_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_inc_ref(v_lctx_1658_);
v___y_1610_ = v_lctx_1658_;
goto v___jp_1609_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v___x_1659_, v___x_1659_);
if (v___x_1661_ == 0)
{
if (v___x_1660_ == 0)
{
lean_inc_ref(v_lctx_1658_);
v___y_1610_ = v_lctx_1658_;
goto v___jp_1609_;
}
else
{
size_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_usize_of_nat(v___x_1659_);
lean_inc_ref(v_lctx_1658_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1608_, v___x_1607_, v___x_1662_, v_lctx_1658_);
v___y_1610_ = v___x_1663_;
goto v___jp_1609_;
}
}
else
{
size_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_usize_of_nat(v___x_1659_);
lean_inc_ref(v_lctx_1658_);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1608_, v___x_1607_, v___x_1664_, v_lctx_1658_);
v___y_1610_ = v___x_1665_;
goto v___jp_1609_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___x_1608_);
lean_dec(v_a_1605_);
lean_dec(v_value_1589_);
v_a_1666_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1657_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1657_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v___x_1648_);
lean_dec_ref(v___x_1608_);
lean_dec(v_a_1605_);
lean_dec(v_value_1589_);
lean_dec(v_type_1588_);
v_a_1674_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1652_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1652_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec_ref(v_xs_1594_);
lean_dec(v_value_1589_);
lean_dec(v_type_1588_);
v_a_1684_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1604_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1604_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1692_, lean_object* v_value_1693_, lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v___y_1697_, lean_object* v_xs_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_99250__boxed_1706_; uint8_t v___x_99251__boxed_1707_; uint8_t v___y_99253__boxed_1708_; lean_object* v_res_1709_; 
v___x_99250__boxed_1706_ = lean_unbox(v___x_1694_);
v___x_99251__boxed_1707_ = lean_unbox(v___x_1695_);
v___y_99253__boxed_1708_ = lean_unbox(v___y_1697_);
v_res_1709_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1692_, v_value_1693_, v___x_99250__boxed_1706_, v___x_99251__boxed_1707_, v___x_1696_, v___y_99253__boxed_1708_, v_xs_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___x_1696_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1710_, lean_object* v_a_1711_, uint8_t v_zeta_1712_, uint8_t v___y_1713_, lean_object* v_x_1714_, uint8_t v_usedOnly_1715_, uint8_t v___x_1716_, uint8_t v___x_1717_, lean_object* v_snd_1718_, lean_object* v_h_x27_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
lean_inc_ref(v_h_x27_1719_);
v___x_1728_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1710_, v_h_x27_1719_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v___x_1728_);
v___x_1729_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1711_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1729_) == 0)
{
if (v_zeta_1712_ == 0)
{
if (v___y_1713_ == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; 
lean_dec_ref(v_snd_1718_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = lean_unsigned_to_nat(2u);
v___x_1732_ = lean_mk_empty_array_with_capacity(v___x_1731_);
v___x_1733_ = lean_array_push(v___x_1732_, v_x_1714_);
v___x_1734_ = lean_array_push(v___x_1733_, v_h_x27_1719_);
v___x_1735_ = 1;
v___x_1736_ = l_Lean_Meta_mkLetFVars(v___x_1734_, v_a_1730_, v_usedOnly_1715_, v___x_1716_, v___x_1735_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec_ref(v___x_1734_);
return v___x_1736_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; 
v_a_1737_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1729_);
v___x_1738_ = lean_unsigned_to_nat(2u);
v___x_1739_ = lean_mk_empty_array_with_capacity(v___x_1738_);
v___x_1740_ = lean_array_push(v___x_1739_, v_x_1714_);
v___x_1741_ = lean_array_push(v___x_1740_, v_h_x27_1719_);
v___x_1742_ = 1;
v___x_1743_ = l_Lean_Meta_mkLambdaFVars(v___x_1741_, v_a_1737_, v___x_1716_, v___x_1717_, v___x_1716_, v___x_1717_, v___x_1742_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec_ref(v___x_1741_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
lean_inc_ref(v_snd_1718_);
v___x_1745_ = l_Lean_Meta_mkEqRefl(v_snd_1718_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l_Lean_mkAppB(v_a_1744_, v_snd_1718_, v_a_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
lean_dec(v_a_1744_);
lean_dec_ref(v_snd_1718_);
return v___x_1745_;
}
}
else
{
lean_dec_ref(v_snd_1718_);
return v___x_1743_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1755_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1729_);
v___x_1756_ = lean_unsigned_to_nat(2u);
v___x_1757_ = lean_mk_empty_array_with_capacity(v___x_1756_);
lean_inc_ref(v___x_1757_);
v___x_1758_ = lean_array_push(v___x_1757_, v_x_1714_);
v___x_1759_ = lean_array_push(v___x_1758_, v_h_x27_1719_);
v___x_1760_ = l_Lean_Expr_abstractM(v_a_1755_, v___x_1759_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec_ref(v___x_1759_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
lean_inc_ref(v_snd_1718_);
v___x_1762_ = l_Lean_Meta_mkEqRefl(v_snd_1718_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1773_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1767_ = lean_array_push(v___x_1757_, v_snd_1718_);
v___x_1768_ = lean_array_push(v___x_1767_, v_a_1763_);
v___x_1769_ = lean_expr_instantiate_rev(v_a_1761_, v___x_1768_);
lean_dec_ref(v___x_1768_);
lean_dec(v_a_1761_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_dec(v_a_1761_);
lean_dec_ref(v___x_1757_);
lean_dec_ref(v_snd_1718_);
return v___x_1762_;
}
}
else
{
lean_dec_ref(v___x_1757_);
lean_dec_ref(v_snd_1718_);
return v___x_1760_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1719_);
lean_dec_ref(v_snd_1718_);
lean_dec_ref(v_x_1714_);
return v___x_1729_;
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v_h_x27_1719_);
lean_dec_ref(v_snd_1718_);
lean_dec_ref(v_x_1714_);
lean_dec_ref(v_a_1711_);
v_a_1774_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1728_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1728_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1782_ = _args[0];
lean_object* v_a_1783_ = _args[1];
lean_object* v_zeta_1784_ = _args[2];
lean_object* v___y_1785_ = _args[3];
lean_object* v_x_1786_ = _args[4];
lean_object* v_usedOnly_1787_ = _args[5];
lean_object* v___x_1788_ = _args[6];
lean_object* v___x_1789_ = _args[7];
lean_object* v_snd_1790_ = _args[8];
lean_object* v_h_x27_1791_ = _args[9];
lean_object* v___y_1792_ = _args[10];
lean_object* v___y_1793_ = _args[11];
lean_object* v___y_1794_ = _args[12];
lean_object* v___y_1795_ = _args[13];
lean_object* v___y_1796_ = _args[14];
lean_object* v___y_1797_ = _args[15];
lean_object* v___y_1798_ = _args[16];
lean_object* v___y_1799_ = _args[17];
_start:
{
uint8_t v_zeta_boxed_1800_; uint8_t v___y_99477__boxed_1801_; uint8_t v_usedOnly_boxed_1802_; uint8_t v___x_99478__boxed_1803_; uint8_t v___x_99479__boxed_1804_; lean_object* v_res_1805_; 
v_zeta_boxed_1800_ = lean_unbox(v_zeta_1784_);
v___y_99477__boxed_1801_ = lean_unbox(v___y_1785_);
v_usedOnly_boxed_1802_ = lean_unbox(v_usedOnly_1787_);
v___x_99478__boxed_1803_ = lean_unbox(v___x_1788_);
v___x_99479__boxed_1804_ = lean_unbox(v___x_1789_);
v_res_1805_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1782_, v_a_1783_, v_zeta_boxed_1800_, v___y_99477__boxed_1801_, v_x_1786_, v_usedOnly_boxed_1802_, v___x_99478__boxed_1803_, v___x_99479__boxed_1804_, v_snd_1790_, v_h_x27_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1806_, lean_object* v_a_1807_, uint8_t v_zeta_1808_, lean_object* v_x_1809_, uint8_t v_usedOnly_1810_, uint8_t v___x_1811_, lean_object* v_snd_1812_, uint8_t v___y_1813_, uint8_t v___x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1806_) == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1807_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
if (v_zeta_1808_ == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_snd_1812_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_mk_empty_array_with_capacity(v___x_1825_);
v___x_1827_ = lean_array_push(v___x_1826_, v_x_1809_);
v___x_1828_ = 1;
v___x_1829_ = l_Lean_Meta_mkLetFVars(v___x_1827_, v_a_1824_, v_usedOnly_1810_, v___x_1811_, v___x_1828_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec_ref(v___x_1827_);
return v___x_1829_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1830_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1823_);
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_mk_empty_array_with_capacity(v___x_1831_);
v___x_1833_ = lean_array_push(v___x_1832_, v_x_1809_);
v___x_1834_ = l_Lean_Expr_abstractM(v_a_1830_, v___x_1833_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec_ref(v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_expr_instantiate1(v_a_1835_, v_snd_1812_);
lean_dec_ref(v_snd_1812_);
lean_dec(v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_dec_ref(v_snd_1812_);
return v___x_1834_;
}
}
}
else
{
lean_dec_ref(v_snd_1812_);
lean_dec_ref(v_x_1809_);
return v___x_1823_;
}
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1845_; 
v_val_1844_ = lean_ctor_get(v_eq_x3f_1806_, 0);
lean_inc(v_val_1844_);
lean_dec_ref(v_eq_x3f_1806_);
lean_inc_ref(v_snd_1812_);
lean_inc_ref(v_x_1809_);
v___x_1845_ = l_Lean_Meta_mkEq(v_x_1809_, v_snd_1812_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
lean_inc_ref(v_x_1809_);
v___x_1847_ = l_Lean_Meta_mkEqRefl(v_x_1809_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___f_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = lean_box(v_zeta_1808_);
v___x_1850_ = lean_box(v___y_1813_);
v___x_1851_ = lean_box(v_usedOnly_1810_);
v___x_1852_ = lean_box(v___x_1811_);
v___x_1853_ = lean_box(v___x_1814_);
lean_inc(v_val_1844_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1854_, 0, v_val_1844_);
lean_closure_set(v___f_1854_, 1, v_a_1807_);
lean_closure_set(v___f_1854_, 2, v___x_1849_);
lean_closure_set(v___f_1854_, 3, v___x_1850_);
lean_closure_set(v___f_1854_, 4, v_x_1809_);
lean_closure_set(v___f_1854_, 5, v___x_1851_);
lean_closure_set(v___f_1854_, 6, v___x_1852_);
lean_closure_set(v___f_1854_, 7, v___x_1853_);
lean_closure_set(v___f_1854_, 8, v_snd_1812_);
v___x_1855_ = l_Lean_TSyntax_getId(v_val_1844_);
lean_dec(v_val_1844_);
v___x_1856_ = 0;
v___x_1857_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1855_, v_a_1846_, v_a_1848_, v___f_1854_, v___x_1814_, v___x_1856_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1857_;
}
else
{
lean_dec(v_a_1846_);
lean_dec(v_val_1844_);
lean_dec_ref(v_snd_1812_);
lean_dec_ref(v_x_1809_);
lean_dec_ref(v_a_1807_);
return v___x_1847_;
}
}
else
{
lean_dec(v_val_1844_);
lean_dec_ref(v_snd_1812_);
lean_dec_ref(v_x_1809_);
lean_dec_ref(v_a_1807_);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_eq_x3f_1858_ = _args[0];
lean_object* v_a_1859_ = _args[1];
lean_object* v_zeta_1860_ = _args[2];
lean_object* v_x_1861_ = _args[3];
lean_object* v_usedOnly_1862_ = _args[4];
lean_object* v___x_1863_ = _args[5];
lean_object* v_snd_1864_ = _args[6];
lean_object* v___y_1865_ = _args[7];
lean_object* v___x_1866_ = _args[8];
lean_object* v___y_1867_ = _args[9];
lean_object* v___y_1868_ = _args[10];
lean_object* v___y_1869_ = _args[11];
lean_object* v___y_1870_ = _args[12];
lean_object* v___y_1871_ = _args[13];
lean_object* v___y_1872_ = _args[14];
lean_object* v___y_1873_ = _args[15];
lean_object* v___y_1874_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1875_; uint8_t v_usedOnly_boxed_1876_; uint8_t v___x_99632__boxed_1877_; uint8_t v___y_99634__boxed_1878_; uint8_t v___x_99635__boxed_1879_; lean_object* v_res_1880_; 
v_zeta_boxed_1875_ = lean_unbox(v_zeta_1860_);
v_usedOnly_boxed_1876_ = lean_unbox(v_usedOnly_1862_);
v___x_99632__boxed_1877_ = lean_unbox(v___x_1863_);
v___y_99634__boxed_1878_ = lean_unbox(v___y_1865_);
v___x_99635__boxed_1879_ = lean_unbox(v___x_1866_);
v_res_1880_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1858_, v_a_1859_, v_zeta_boxed_1875_, v_x_1861_, v_usedOnly_boxed_1876_, v___x_99632__boxed_1877_, v_snd_1864_, v___y_99634__boxed_1878_, v___x_99635__boxed_1879_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1881_, lean_object* v_eq_x3f_1882_, lean_object* v_a_1883_, uint8_t v_zeta_1884_, uint8_t v_usedOnly_1885_, uint8_t v___x_1886_, lean_object* v_snd_1887_, uint8_t v___y_1888_, uint8_t v___x_1889_, lean_object* v_letOrReassign_1890_, lean_object* v_a_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
lean_inc_ref(v_x_1892_);
v___x_1901_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1881_, v_x_1892_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___y_1907_; lean_object* v___x_1908_; 
lean_dec_ref(v___x_1901_);
v___x_1902_ = lean_box(v_zeta_1884_);
v___x_1903_ = lean_box(v_usedOnly_1885_);
v___x_1904_ = lean_box(v___x_1886_);
v___x_1905_ = lean_box(v___y_1888_);
v___x_1906_ = lean_box(v___x_1889_);
v___y_1907_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 17, 9);
lean_closure_set(v___y_1907_, 0, v_eq_x3f_1882_);
lean_closure_set(v___y_1907_, 1, v_a_1883_);
lean_closure_set(v___y_1907_, 2, v___x_1902_);
lean_closure_set(v___y_1907_, 3, v_x_1892_);
lean_closure_set(v___y_1907_, 4, v___x_1903_);
lean_closure_set(v___y_1907_, 5, v___x_1904_);
lean_closure_set(v___y_1907_, 6, v_snd_1887_);
lean_closure_set(v___y_1907_, 7, v___x_1905_);
lean_closure_set(v___y_1907_, 8, v___x_1906_);
v___x_1908_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1890_, v_a_1891_, v___y_1907_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1908_;
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v_x_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_letOrReassign_1890_);
lean_dec_ref(v_snd_1887_);
lean_dec_ref(v_a_1883_);
lean_dec(v_eq_x3f_1882_);
v_a_1909_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1901_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1901_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1917_ = _args[0];
lean_object* v_eq_x3f_1918_ = _args[1];
lean_object* v_a_1919_ = _args[2];
lean_object* v_zeta_1920_ = _args[3];
lean_object* v_usedOnly_1921_ = _args[4];
lean_object* v___x_1922_ = _args[5];
lean_object* v_snd_1923_ = _args[6];
lean_object* v___y_1924_ = _args[7];
lean_object* v___x_1925_ = _args[8];
lean_object* v_letOrReassign_1926_ = _args[9];
lean_object* v_a_1927_ = _args[10];
lean_object* v_x_1928_ = _args[11];
lean_object* v___y_1929_ = _args[12];
lean_object* v___y_1930_ = _args[13];
lean_object* v___y_1931_ = _args[14];
lean_object* v___y_1932_ = _args[15];
lean_object* v___y_1933_ = _args[16];
lean_object* v___y_1934_ = _args[17];
lean_object* v___y_1935_ = _args[18];
lean_object* v___y_1936_ = _args[19];
_start:
{
uint8_t v_zeta_boxed_1937_; uint8_t v_usedOnly_boxed_1938_; uint8_t v___x_99745__boxed_1939_; uint8_t v___y_99747__boxed_1940_; uint8_t v___x_99748__boxed_1941_; lean_object* v_res_1942_; 
v_zeta_boxed_1937_ = lean_unbox(v_zeta_1920_);
v_usedOnly_boxed_1938_ = lean_unbox(v_usedOnly_1921_);
v___x_99745__boxed_1939_ = lean_unbox(v___x_1922_);
v___y_99747__boxed_1940_ = lean_unbox(v___y_1924_);
v___x_99748__boxed_1941_ = lean_unbox(v___x_1925_);
v_res_1942_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1917_, v_eq_x3f_1918_, v_a_1919_, v_zeta_boxed_1937_, v_usedOnly_boxed_1938_, v___x_99745__boxed_1939_, v_snd_1923_, v___y_99747__boxed_1940_, v___x_99748__boxed_1941_, v_letOrReassign_1926_, v_a_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1943_, lean_object* v_____do__lift_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1944_, v___x_1943_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1955_, lean_object* v_____do__lift_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_99819__boxed_1965_; lean_object* v_res_1966_; 
v___x_99819__boxed_1965_ = lean_unbox(v___x_1955_);
v_res_1966_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99819__boxed_1965_, v_____do__lift_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v_____do__lift_1956_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1967_, lean_object* v___x_1968_, uint8_t v___x_1969_, lean_object* v___x_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1967_, v___x_1968_, v___x_1969_, v___x_1969_, v___x_1970_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1980_, lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v___x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v___x_99854__boxed_1992_; lean_object* v_res_1993_; 
v___x_99854__boxed_1992_ = lean_unbox(v___x_1982_);
v_res_1993_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1980_, v___x_1981_, v___x_99854__boxed_1992_, v___x_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
lean_inc_ref(v___y_1995_);
v___x_2003_ = lean_apply_8(v_x_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, lean_box(0));
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec_ref(v___y_2005_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_2014_, lean_object* v_mkInfoTree_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v_a_2021_, lean_object* v_a_x3f_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v_infoState_2025_; lean_object* v_trees_2026_; lean_object* v___x_2027_; 
v___x_2024_ = lean_st_ref_get(v___y_2014_);
v_infoState_2025_ = lean_ctor_get(v___x_2024_, 7);
lean_inc_ref(v_infoState_2025_);
lean_dec(v___x_2024_);
v_trees_2026_ = lean_ctor_get(v_infoState_2025_, 2);
lean_inc_ref(v_trees_2026_);
lean_dec_ref(v_infoState_2025_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
v___x_2027_ = lean_apply_8(v_mkInfoTree_2015_, v_trees_2026_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2014_, lean_box(0));
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2067_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2067_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2067_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v_infoState_2033_; lean_object* v_env_2034_; lean_object* v_nextMacroScope_2035_; lean_object* v_ngen_2036_; lean_object* v_auxDeclNGen_2037_; lean_object* v_traceState_2038_; lean_object* v_cache_2039_; lean_object* v_messages_2040_; lean_object* v_snapshotTasks_2041_; lean_object* v_newDecls_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2066_; 
v___x_2032_ = lean_st_ref_take(v___y_2014_);
v_infoState_2033_ = lean_ctor_get(v___x_2032_, 7);
v_env_2034_ = lean_ctor_get(v___x_2032_, 0);
v_nextMacroScope_2035_ = lean_ctor_get(v___x_2032_, 1);
v_ngen_2036_ = lean_ctor_get(v___x_2032_, 2);
v_auxDeclNGen_2037_ = lean_ctor_get(v___x_2032_, 3);
v_traceState_2038_ = lean_ctor_get(v___x_2032_, 4);
v_cache_2039_ = lean_ctor_get(v___x_2032_, 5);
v_messages_2040_ = lean_ctor_get(v___x_2032_, 6);
v_snapshotTasks_2041_ = lean_ctor_get(v___x_2032_, 8);
v_newDecls_2042_ = lean_ctor_get(v___x_2032_, 9);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2044_ = v___x_2032_;
v_isShared_2045_ = v_isSharedCheck_2066_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_newDecls_2042_);
lean_inc(v_snapshotTasks_2041_);
lean_inc(v_infoState_2033_);
lean_inc(v_messages_2040_);
lean_inc(v_cache_2039_);
lean_inc(v_traceState_2038_);
lean_inc(v_auxDeclNGen_2037_);
lean_inc(v_ngen_2036_);
lean_inc(v_nextMacroScope_2035_);
lean_inc(v_env_2034_);
lean_dec(v___x_2032_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2066_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint8_t v_enabled_2046_; lean_object* v_assignment_2047_; lean_object* v_lazyAssignment_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2064_; 
v_enabled_2046_ = lean_ctor_get_uint8(v_infoState_2033_, sizeof(void*)*3);
v_assignment_2047_ = lean_ctor_get(v_infoState_2033_, 0);
v_lazyAssignment_2048_ = lean_ctor_get(v_infoState_2033_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_infoState_2033_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_infoState_2033_, 2);
lean_dec(v_unused_2065_);
v___x_2050_ = v_infoState_2033_;
v_isShared_2051_ = v_isSharedCheck_2064_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_lazyAssignment_2048_);
lean_inc(v_assignment_2047_);
lean_dec(v_infoState_2033_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2064_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_PersistentArray_push___redArg(v_a_2021_, v_a_2028_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 2, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_assignment_2047_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_lazyAssignment_2048_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v___x_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_enabled_2046_);
v___x_2054_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 7, v___x_2054_);
v___x_2056_ = v___x_2044_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_env_2034_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_nextMacroScope_2035_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_ngen_2036_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_auxDeclNGen_2037_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_traceState_2038_);
lean_ctor_set(v_reuseFailAlloc_2062_, 5, v_cache_2039_);
lean_ctor_set(v_reuseFailAlloc_2062_, 6, v_messages_2040_);
lean_ctor_set(v_reuseFailAlloc_2062_, 7, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2062_, 8, v_snapshotTasks_2041_);
lean_ctor_set(v_reuseFailAlloc_2062_, 9, v_newDecls_2042_);
v___x_2056_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2057_ = lean_st_ref_set(v___y_2014_, v___x_2056_);
v___x_2058_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2058_);
v___x_2060_ = v___x_2030_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_a_2021_);
v_a_2068_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2027_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2027_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_2076_, lean_object* v_mkInfoTree_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v_a_2083_, lean_object* v_a_x3f_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2076_, v_mkInfoTree_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v_a_2083_, v_a_x3f_2084_);
lean_dec(v_a_x3f_2084_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2076_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v_infoState_2090_; lean_object* v_trees_2091_; lean_object* v___x_2092_; lean_object* v_infoState_2093_; lean_object* v_env_2094_; lean_object* v_nextMacroScope_2095_; lean_object* v_ngen_2096_; lean_object* v_auxDeclNGen_2097_; lean_object* v_traceState_2098_; lean_object* v_cache_2099_; lean_object* v_messages_2100_; lean_object* v_snapshotTasks_2101_; lean_object* v_newDecls_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2125_; 
v___x_2089_ = lean_st_ref_get(v___y_2087_);
v_infoState_2090_ = lean_ctor_get(v___x_2089_, 7);
lean_inc_ref(v_infoState_2090_);
lean_dec(v___x_2089_);
v_trees_2091_ = lean_ctor_get(v_infoState_2090_, 2);
lean_inc_ref(v_trees_2091_);
lean_dec_ref(v_infoState_2090_);
v___x_2092_ = lean_st_ref_take(v___y_2087_);
v_infoState_2093_ = lean_ctor_get(v___x_2092_, 7);
v_env_2094_ = lean_ctor_get(v___x_2092_, 0);
v_nextMacroScope_2095_ = lean_ctor_get(v___x_2092_, 1);
v_ngen_2096_ = lean_ctor_get(v___x_2092_, 2);
v_auxDeclNGen_2097_ = lean_ctor_get(v___x_2092_, 3);
v_traceState_2098_ = lean_ctor_get(v___x_2092_, 4);
v_cache_2099_ = lean_ctor_get(v___x_2092_, 5);
v_messages_2100_ = lean_ctor_get(v___x_2092_, 6);
v_snapshotTasks_2101_ = lean_ctor_get(v___x_2092_, 8);
v_newDecls_2102_ = lean_ctor_get(v___x_2092_, 9);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2104_ = v___x_2092_;
v_isShared_2105_ = v_isSharedCheck_2125_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_newDecls_2102_);
lean_inc(v_snapshotTasks_2101_);
lean_inc(v_infoState_2093_);
lean_inc(v_messages_2100_);
lean_inc(v_cache_2099_);
lean_inc(v_traceState_2098_);
lean_inc(v_auxDeclNGen_2097_);
lean_inc(v_ngen_2096_);
lean_inc(v_nextMacroScope_2095_);
lean_inc(v_env_2094_);
lean_dec(v___x_2092_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2125_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
uint8_t v_enabled_2106_; lean_object* v_assignment_2107_; lean_object* v_lazyAssignment_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2123_; 
v_enabled_2106_ = lean_ctor_get_uint8(v_infoState_2093_, sizeof(void*)*3);
v_assignment_2107_ = lean_ctor_get(v_infoState_2093_, 0);
v_lazyAssignment_2108_ = lean_ctor_get(v_infoState_2093_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_infoState_2093_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v_infoState_2093_, 2);
lean_dec(v_unused_2124_);
v___x_2110_ = v_infoState_2093_;
v_isShared_2111_ = v_isSharedCheck_2123_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_lazyAssignment_2108_);
lean_inc(v_assignment_2107_);
lean_dec(v_infoState_2093_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2123_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2112_ = lean_unsigned_to_nat(32u);
v___x_2113_ = lean_mk_empty_array_with_capacity(v___x_2112_);
lean_dec_ref(v___x_2113_);
v___x_2114_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___closed__1);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 2, v___x_2114_);
v___x_2116_ = v___x_2110_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_assignment_2107_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_lazyAssignment_2108_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v___x_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, sizeof(void*)*3, v_enabled_2106_);
v___x_2116_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 7, v___x_2116_);
v___x_2118_ = v___x_2104_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_env_2094_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_nextMacroScope_2095_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_ngen_2096_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_auxDeclNGen_2097_);
lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_traceState_2098_);
lean_ctor_set(v_reuseFailAlloc_2121_, 5, v_cache_2099_);
lean_ctor_set(v_reuseFailAlloc_2121_, 6, v_messages_2100_);
lean_ctor_set(v_reuseFailAlloc_2121_, 7, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2121_, 8, v_snapshotTasks_2101_);
lean_ctor_set(v_reuseFailAlloc_2121_, 9, v_newDecls_2102_);
v___x_2118_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_st_ref_set(v___y_2087_, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_trees_2091_);
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2126_);
lean_dec(v___y_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_2129_, lean_object* v_mkInfoTree_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v_infoState_2139_; uint8_t v_enabled_2140_; 
v___x_2138_ = lean_st_ref_get(v___y_2136_);
v_infoState_2139_ = lean_ctor_get(v___x_2138_, 7);
lean_inc_ref(v_infoState_2139_);
lean_dec(v___x_2138_);
v_enabled_2140_ = lean_ctor_get_uint8(v_infoState_2139_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2139_);
if (v_enabled_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec_ref(v_mkInfoTree_2130_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
v___x_2141_ = lean_apply_7(v_x_2129_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, lean_box(0));
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v_a_2143_; lean_object* v_r_2144_; 
v___x_2142_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2136_);
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
v_r_2144_ = lean_apply_7(v_x_2129_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, lean_box(0));
if (lean_obj_tag(v_r_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2169_; 
v_a_2145_ = lean_ctor_get(v_r_2144_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_r_2144_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2147_ = v_r_2144_;
v_isShared_2148_ = v_isSharedCheck_2169_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v_r_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2169_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
lean_inc(v_a_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 1);
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2136_, v_mkInfoTree_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v_a_2143_, v___x_2150_);
lean_dec_ref(v___x_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2159_);
v___x_2153_ = v___x_2151_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2151_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v_a_2145_);
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2145_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2145_);
v_a_2160_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2151_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v_r_2144_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v_r_2144_);
v___x_2171_ = lean_box(0);
v___x_2172_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2136_, v_mkInfoTree_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v_a_2143_, v___x_2171_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v___x_2172_, 0);
lean_dec(v_unused_2180_);
v___x_2174_ = v___x_2172_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v___x_2172_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 1);
lean_ctor_set(v___x_2174_, 0, v_a_2170_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2170_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_a_2170_);
v_a_2181_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2172_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2172_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_2189_, lean_object* v_mkInfoTree_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2189_, v_mkInfoTree_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2199_, lean_object* v_output_2200_, lean_object* v_trees_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_lctx_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_lctx_2209_ = lean_ctor_get(v___y_2204_, 2);
lean_inc_ref(v_lctx_2209_);
v___x_2210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2210_, 0, v_lctx_2209_);
lean_ctor_set(v___x_2210_, 1, v_stx_2199_);
lean_ctor_set(v___x_2210_, 2, v_output_2200_);
v___x_2211_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v_trees_2201_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2214_, lean_object* v_output_2215_, lean_object* v_trees_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2214_, v_output_2215_, v_trees_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2225_, lean_object* v_output_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___f_2235_; lean_object* v___x_2236_; 
v___f_2235_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2235_, 0, v_stx_2225_);
lean_closure_set(v___f_2235_, 1, v_output_2226_);
v___x_2236_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2227_, v___f_2235_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2237_, lean_object* v_output_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2237_, v_output_2238_, v_x_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2248_, lean_object* v_afterStx_2249_, lean_object* v_x_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_inc_ref(v___y_2251_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2259_, 0, v_x_2250_);
lean_closure_set(v___f_2259_, 1, v___y_2251_);
lean_inc(v_afterStx_2249_);
lean_inc(v_beforeStx_2248_);
v___x_2260_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2260_, 0, lean_box(0));
lean_closure_set(v___x_2260_, 1, v_beforeStx_2248_);
lean_closure_set(v___x_2260_, 2, v_afterStx_2249_);
lean_closure_set(v___x_2260_, 3, v___f_2259_);
v___x_2261_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2248_, v_afterStx_2249_, v___x_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2261_) == 0)
{
return v___x_2261_;
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2270_, lean_object* v_afterStx_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2270_, v_afterStx_2271_, v_x_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2281_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2285_ = l_String_toRawSubstring_x27(v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2307_, uint8_t v___x_2308_, lean_object* v_config_2309_, lean_object* v_a_2310_, uint8_t v___x_2311_, lean_object* v___x_2312_, lean_object* v___x_2313_, lean_object* v___x_2314_, lean_object* v___f_2315_, lean_object* v___x_2316_, lean_object* v_body_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_term_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v_ref_2334_; lean_object* v___y_2335_; lean_object* v_ref_2341_; lean_object* v_quotContext_2342_; lean_object* v_currMacroScope_2343_; lean_object* v_ref_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_eq_x3f_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_ref_2341_ = lean_ctor_get(v___y_2323_, 5);
v_quotContext_2342_ = lean_ctor_get(v___y_2323_, 10);
v_currMacroScope_2343_ = lean_ctor_get(v___y_2323_, 11);
v_ref_2344_ = l_Lean_replaceRef(v_rhs_2307_, v_ref_2341_);
v___x_2345_ = l_Lean_SourceInfo_fromRef(v_ref_2344_, v___x_2308_);
lean_dec(v_ref_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2345_, 2);
v___x_2347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2349_ = lean_ctor_get(v_config_2309_, 0);
lean_inc(v_eq_x3f_2349_);
lean_dec_ref(v_config_2309_);
v___x_2350_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2343_);
lean_inc(v_quotContext_2342_);
v___x_2351_ = l_Lean_addMacroScope(v_quotContext_2342_, v___x_2350_, v_currMacroScope_2343_);
v___x_2352_ = lean_box(0);
lean_inc(v___x_2351_);
v___x_2353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2345_);
lean_ctor_set(v___x_2353_, 1, v___x_2348_);
lean_ctor_set(v___x_2353_, 2, v___x_2351_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
v___x_2354_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2314_);
lean_inc_ref(v___x_2313_);
lean_inc_ref(v___x_2312_);
v___x_2355_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2354_);
v___x_2356_ = l_Lean_Syntax_node2(v___x_2345_, v___x_2355_, v___x_2347_, v___x_2353_);
if (lean_obj_tag(v_eq_x3f_2349_) == 1)
{
lean_object* v_val_2357_; lean_object* v___x_2358_; 
v_val_2357_ = lean_ctor_get(v_eq_x3f_2349_, 0);
lean_inc(v_val_2357_);
lean_dec_ref(v_eq_x3f_2349_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
lean_inc(v___y_2322_);
lean_inc_ref(v___y_2321_);
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v_ref_2341_);
v___x_2358_ = lean_apply_9(v___f_2315_, v_ref_2341_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, lean_box(0));
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_n(v_a_2359_, 23);
lean_dec_ref(v___x_2358_);
v___x_2360_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2314_, 5);
lean_inc_ref_n(v___x_2313_, 5);
lean_inc_ref_n(v___x_2312_, 5);
v___x_2361_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2360_);
v___x_2362_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2363_, 0, v_a_2359_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2359_);
lean_ctor_set(v___x_2364_, 1, v___x_2346_);
v___x_2365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2365_, 0, v_a_2359_);
lean_ctor_set(v___x_2365_, 1, v___x_2348_);
lean_ctor_set(v___x_2365_, 2, v___x_2351_);
lean_ctor_set(v___x_2365_, 3, v___x_2352_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2359_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2359_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2371_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_a_2359_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2375_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_a_2359_);
lean_ctor_set(v___x_2376_, 1, v___x_2374_);
v___x_2377_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2378_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2379_, 0, v_a_2359_);
lean_ctor_set(v___x_2379_, 1, v___x_2377_);
lean_ctor_set(v___x_2379_, 2, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2381_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2380_);
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2359_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node2(v_a_2359_, v___x_2377_, v_val_2357_, v___x_2383_);
v___x_2385_ = l_Lean_Syntax_node2(v_a_2359_, v___x_2381_, v___x_2384_, v___x_2356_);
v___x_2386_ = l_Lean_Syntax_node1(v_a_2359_, v___x_2377_, v___x_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_a_2359_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2390_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2389_);
v___x_2391_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2392_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_a_2359_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_Syntax_node1(v_a_2359_, v___x_2377_, v___x_2316_);
v___x_2396_ = l_Lean_Syntax_node1(v_a_2359_, v___x_2377_, v___x_2395_);
v___x_2397_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_a_2359_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Lean_Syntax_node4(v_a_2359_, v___x_2392_, v___x_2394_, v___x_2396_, v___x_2398_, v_body_2317_);
v___x_2400_ = l_Lean_Syntax_node1(v_a_2359_, v___x_2377_, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node1(v_a_2359_, v___x_2390_, v___x_2400_);
lean_inc_ref(v___x_2379_);
v___x_2402_ = l_Lean_Syntax_node6(v_a_2359_, v___x_2375_, v___x_2376_, v___x_2379_, v___x_2379_, v___x_2386_, v___x_2388_, v___x_2401_);
lean_inc_ref(v___x_2369_);
lean_inc_ref(v___x_2365_);
lean_inc_ref(v___x_2364_);
v___x_2403_ = l_Lean_Syntax_node5(v_a_2359_, v___x_2371_, v___x_2373_, v___x_2364_, v___x_2365_, v___x_2369_, v___x_2402_);
v___x_2404_ = l_Lean_Syntax_node7(v_a_2359_, v___x_2361_, v___x_2363_, v___x_2364_, v___x_2365_, v___x_2367_, v_rhs_2307_, v___x_2369_, v___x_2403_);
lean_inc(v_ref_2341_);
v_term_2327_ = v___x_2404_;
v___y_2328_ = v___y_2318_;
v___y_2329_ = v___y_2319_;
v___y_2330_ = v___y_2320_;
v___y_2331_ = v___y_2321_;
v___y_2332_ = v___y_2322_;
v___y_2333_ = v___y_2323_;
v_ref_2334_ = v_ref_2341_;
v___y_2335_ = v___y_2324_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_val_2357_);
lean_dec(v___x_2356_);
lean_dec(v___x_2351_);
lean_dec(v_body_2317_);
lean_dec(v___x_2316_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_a_2310_);
lean_dec(v_rhs_2307_);
v_a_2405_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2358_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2358_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v___x_2413_; 
lean_dec(v_eq_x3f_2349_);
lean_inc_ref(v_a_2310_);
v___x_2413_ = l_Lean_Elab_Term_exprToSyntax(v_a_2310_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref(v___x_2413_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
lean_inc(v___y_2322_);
lean_inc_ref(v___y_2321_);
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v_ref_2341_);
v___x_2415_ = lean_apply_9(v___f_2315_, v_ref_2341_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, lean_box(0));
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_n(v_a_2416_, 32);
lean_dec_ref(v___x_2415_);
v___x_2417_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2314_, 8);
lean_inc_ref_n(v___x_2313_, 8);
lean_inc_ref_n(v___x_2312_, 8);
v___x_2418_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2417_);
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_a_2416_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2416_);
lean_ctor_set(v___x_2421_, 1, v___x_2346_);
v___x_2422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2422_, 0, v_a_2416_);
lean_ctor_set(v___x_2422_, 1, v___x_2348_);
lean_ctor_set(v___x_2422_, 2, v___x_2351_);
lean_ctor_set(v___x_2422_, 3, v___x_2352_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2416_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2426_, 0, v_a_2416_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2428_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2416_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2432_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2416_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
v___x_2434_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2435_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2416_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
lean_ctor_set(v___x_2436_, 2, v___x_2435_);
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2438_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2437_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_a_2416_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2416_);
lean_ctor_set(v___x_2441_, 1, v___x_2437_);
v___x_2442_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2443_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v_a_2416_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2447_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_a_2416_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2447_, v___x_2449_);
v___x_2451_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2416_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_inc_ref_n(v___x_2436_, 2);
v___x_2454_ = l_Lean_Syntax_node5(v_a_2416_, v___x_2443_, v___x_2445_, v___x_2451_, v___x_2436_, v___x_2453_, v_a_2414_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_a_2416_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc_ref(v___x_2424_);
v___x_2457_ = l_Lean_Syntax_node5(v_a_2416_, v___x_2438_, v___x_2440_, v___x_2441_, v___x_2424_, v___x_2454_, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2460_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2459_);
v___x_2461_ = l_Lean_Syntax_node2(v_a_2416_, v___x_2460_, v___x_2436_, v___x_2356_);
v___x_2462_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2461_);
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_a_2416_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2466_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2465_);
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2468_ = l_Lean_Name_mkStr4(v___x_2312_, v___x_2313_, v___x_2314_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2416_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2316_);
v___x_2472_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2471_);
v___x_2473_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2416_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node4(v_a_2416_, v___x_2468_, v___x_2470_, v___x_2472_, v___x_2474_, v_body_2317_);
v___x_2476_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2434_, v___x_2475_);
v___x_2477_ = l_Lean_Syntax_node1(v_a_2416_, v___x_2466_, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node6(v_a_2416_, v___x_2432_, v___x_2433_, v___x_2436_, v___x_2458_, v___x_2462_, v___x_2464_, v___x_2477_);
lean_inc_ref(v___x_2426_);
lean_inc_ref(v___x_2422_);
lean_inc_ref(v___x_2421_);
v___x_2479_ = l_Lean_Syntax_node5(v_a_2416_, v___x_2428_, v___x_2430_, v___x_2421_, v___x_2422_, v___x_2426_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node7(v_a_2416_, v___x_2418_, v___x_2420_, v___x_2421_, v___x_2422_, v___x_2424_, v_rhs_2307_, v___x_2426_, v___x_2479_);
lean_inc(v_ref_2341_);
v_term_2327_ = v___x_2480_;
v___y_2328_ = v___y_2318_;
v___y_2329_ = v___y_2319_;
v___y_2330_ = v___y_2320_;
v___y_2331_ = v___y_2321_;
v___y_2332_ = v___y_2322_;
v___y_2333_ = v___y_2323_;
v_ref_2334_ = v_ref_2341_;
v___y_2335_ = v___y_2324_;
goto v___jp_2326_;
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_a_2414_);
lean_dec(v___x_2356_);
lean_dec(v___x_2351_);
lean_dec(v_body_2317_);
lean_dec(v___x_2316_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_a_2310_);
lean_dec(v_rhs_2307_);
v_a_2481_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2415_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2415_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v___x_2356_);
lean_dec(v___x_2351_);
lean_dec(v_body_2317_);
lean_dec(v___x_2316_);
lean_dec_ref(v___f_2315_);
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2313_);
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_a_2310_);
lean_dec(v_rhs_2307_);
v_a_2489_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2413_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2413_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
v___jp_2326_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; 
v___x_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2310_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_box(v___x_2311_);
lean_inc(v_term_2327_);
v___f_2339_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2339_, 0, v_term_2327_);
lean_closure_set(v___f_2339_, 1, v___x_2336_);
lean_closure_set(v___f_2339_, 2, v___x_2338_);
lean_closure_set(v___f_2339_, 3, v___x_2337_);
v___x_2340_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2334_, v_term_2327_, v___f_2339_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2335_);
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2497_ = _args[0];
lean_object* v___x_2498_ = _args[1];
lean_object* v_config_2499_ = _args[2];
lean_object* v_a_2500_ = _args[3];
lean_object* v___x_2501_ = _args[4];
lean_object* v___x_2502_ = _args[5];
lean_object* v___x_2503_ = _args[6];
lean_object* v___x_2504_ = _args[7];
lean_object* v___f_2505_ = _args[8];
lean_object* v___x_2506_ = _args[9];
lean_object* v_body_2507_ = _args[10];
lean_object* v___y_2508_ = _args[11];
lean_object* v___y_2509_ = _args[12];
lean_object* v___y_2510_ = _args[13];
lean_object* v___y_2511_ = _args[14];
lean_object* v___y_2512_ = _args[15];
lean_object* v___y_2513_ = _args[16];
lean_object* v___y_2514_ = _args[17];
lean_object* v___y_2515_ = _args[18];
_start:
{
uint8_t v___x_100371__boxed_2516_; uint8_t v___x_100373__boxed_2517_; lean_object* v_res_2518_; 
v___x_100371__boxed_2516_ = lean_unbox(v___x_2498_);
v___x_100373__boxed_2517_ = lean_unbox(v___x_2501_);
v_res_2518_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2497_, v___x_100371__boxed_2516_, v_config_2499_, v_a_2500_, v___x_100373__boxed_2517_, v___x_2502_, v___x_2503_, v___x_2504_, v___f_2505_, v___x_2506_, v_body_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2519_, lean_object* v___y_2520_){
_start:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
v_a_2521_ = lean_ctor_get(v_x_2519_, 0);
lean_inc(v_a_2521_);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2521_);
lean_ctor_set(v___x_2522_, 1, v___y_2520_);
return v___x_2522_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v_x_2519_, 0);
lean_inc(v_a_2523_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_a_2523_);
lean_ctor_set(v___x_2524_, 1, v___y_2520_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2525_, v___y_2526_);
lean_dec_ref(v_x_2525_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2528_, lean_object* v_stx_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2528_, v_stx_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
if (lean_obj_tag(v_a_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v_a_2534_ = lean_ctor_get(v___x_2532_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2532_, 0);
lean_dec(v_unused_2543_);
v___x_2536_ = v___x_2532_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2532_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_box(0);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_a_2534_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_val_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2572_; 
v_val_2544_ = lean_ctor_get(v_a_2533_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2546_ = v_a_2533_;
v_isShared_2547_ = v_isSharedCheck_2572_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_val_2544_);
lean_dec(v_a_2533_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2572_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_snd_2548_; 
v_snd_2548_ = lean_ctor_get(v_val_2544_, 1);
lean_inc(v_snd_2548_);
lean_dec(v_val_2544_);
if (lean_obj_tag(v_snd_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
lean_del_object(v___x_2546_);
v_a_2549_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2532_);
v_a_2550_ = lean_ctor_get(v_snd_2548_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_snd_2548_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v_snd_2548_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v_snd_2548_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2555_, v_a_2549_);
lean_dec_ref(v___x_2555_);
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2571_; 
v_a_2559_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2532_);
v_a_2560_ = lean_ctor_get(v_snd_2548_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_snd_2548_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2562_ = v_snd_2548_;
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v_snd_2548_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v_a_2560_);
v___x_2565_ = v___x_2546_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2567_, v_a_2559_);
lean_dec_ref(v___x_2567_);
return v___x_2568_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2573_ = lean_ctor_get(v___x_2532_, 0);
v_a_2574_ = lean_ctor_get(v___x_2532_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2532_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_inc(v_a_2573_);
lean_dec(v___x_2532_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2573_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2582_, lean_object* v_stx_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2582_, v_stx_2583_, v___y_2584_, v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_currNamespace_2587_);
lean_ctor_set(v___x_2590_, 1, v___y_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2591_, v___y_2592_, v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2595_, lean_object* v_currNamespace_2596_, lean_object* v_openDecls_2597_, lean_object* v_n_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = l_Lean_ResolveName_resolveNamespace(v_env_2595_, v_currNamespace_2596_, v_openDecls_2597_, v_n_2598_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2603_, lean_object* v_currNamespace_2604_, lean_object* v_openDecls_2605_, lean_object* v_n_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2603_, v_currNamespace_2604_, v_openDecls_2605_, v_n_2606_, v___y_2607_, v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2610_, lean_object* v_declName_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v___x_2614_; lean_object* v_env_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2614_ = 0;
v_env_2615_ = l_Lean_Environment_setExporting(v_env_2610_, v___x_2614_);
lean_inc(v_declName_2611_);
v___x_2616_ = l_Lean_mkPrivateName(v_env_2615_, v_declName_2611_);
v___x_2617_ = 1;
lean_inc_ref(v_env_2615_);
v___x_2618_ = l_Lean_Environment_contains(v_env_2615_, v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; uint8_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2619_ = l_Lean_privateToUserName(v_declName_2611_);
v___x_2620_ = l_Lean_Environment_contains(v_env_2615_, v___x_2619_, v___x_2617_);
v___x_2621_ = lean_box(v___x_2620_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___y_2613_);
return v___x_2622_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v_env_2615_);
lean_dec(v_declName_2611_);
v___x_2623_ = lean_box(v___x_2618_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___y_2613_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2625_, lean_object* v_declName_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2625_, v_declName_2626_, v___y_2627_, v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2629_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2630_; double v___x_2631_; 
v___x_2630_ = lean_unsigned_to_nat(0u);
v___x_2631_ = lean_float_of_nat(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2634_, lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_ref_2641_; lean_object* v___x_2642_; lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2688_; 
v_ref_2641_ = lean_ctor_get(v___y_2638_, 5);
v___x_2642_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2688_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2688_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v_traceState_2648_; lean_object* v_env_2649_; lean_object* v_nextMacroScope_2650_; lean_object* v_ngen_2651_; lean_object* v_auxDeclNGen_2652_; lean_object* v_cache_2653_; lean_object* v_messages_2654_; lean_object* v_infoState_2655_; lean_object* v_snapshotTasks_2656_; lean_object* v_newDecls_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2687_; 
v___x_2647_ = lean_st_ref_take(v___y_2639_);
v_traceState_2648_ = lean_ctor_get(v___x_2647_, 4);
v_env_2649_ = lean_ctor_get(v___x_2647_, 0);
v_nextMacroScope_2650_ = lean_ctor_get(v___x_2647_, 1);
v_ngen_2651_ = lean_ctor_get(v___x_2647_, 2);
v_auxDeclNGen_2652_ = lean_ctor_get(v___x_2647_, 3);
v_cache_2653_ = lean_ctor_get(v___x_2647_, 5);
v_messages_2654_ = lean_ctor_get(v___x_2647_, 6);
v_infoState_2655_ = lean_ctor_get(v___x_2647_, 7);
v_snapshotTasks_2656_ = lean_ctor_get(v___x_2647_, 8);
v_newDecls_2657_ = lean_ctor_get(v___x_2647_, 9);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2659_ = v___x_2647_;
v_isShared_2660_ = v_isSharedCheck_2687_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_newDecls_2657_);
lean_inc(v_snapshotTasks_2656_);
lean_inc(v_infoState_2655_);
lean_inc(v_messages_2654_);
lean_inc(v_cache_2653_);
lean_inc(v_traceState_2648_);
lean_inc(v_auxDeclNGen_2652_);
lean_inc(v_ngen_2651_);
lean_inc(v_nextMacroScope_2650_);
lean_inc(v_env_2649_);
lean_dec(v___x_2647_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2687_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
uint64_t v_tid_2661_; lean_object* v_traces_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2686_; 
v_tid_2661_ = lean_ctor_get_uint64(v_traceState_2648_, sizeof(void*)*1);
v_traces_2662_ = lean_ctor_get(v_traceState_2648_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_traceState_2648_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2664_ = v_traceState_2648_;
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_traces_2662_);
lean_dec(v_traceState_2648_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; double v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2668_ = 0;
v___x_2669_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2670_, 0, v_cls_2634_);
lean_ctor_set(v___x_2670_, 1, v___x_2666_);
lean_ctor_set(v___x_2670_, 2, v___x_2669_);
lean_ctor_set_float(v___x_2670_, sizeof(void*)*3, v___x_2667_);
lean_ctor_set_float(v___x_2670_, sizeof(void*)*3 + 8, v___x_2667_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*3 + 16, v___x_2668_);
v___x_2671_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2672_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v_a_2643_);
lean_ctor_set(v___x_2672_, 2, v___x_2671_);
lean_inc(v_ref_2641_);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_ref_2641_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_PersistentArray_push___redArg(v_traces_2662_, v___x_2673_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2674_);
v___x_2676_ = v___x_2664_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2674_);
lean_ctor_set_uint64(v_reuseFailAlloc_2685_, sizeof(void*)*1, v_tid_2661_);
v___x_2676_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 4, v___x_2676_);
v___x_2678_ = v___x_2659_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_env_2649_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_nextMacroScope_2650_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_ngen_2651_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_auxDeclNGen_2652_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2684_, 5, v_cache_2653_);
lean_ctor_set(v_reuseFailAlloc_2684_, 6, v_messages_2654_);
lean_ctor_set(v_reuseFailAlloc_2684_, 7, v_infoState_2655_);
lean_ctor_set(v_reuseFailAlloc_2684_, 8, v_snapshotTasks_2656_);
lean_ctor_set(v_reuseFailAlloc_2684_, 9, v_newDecls_2657_);
v___x_2678_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2679_ = lean_st_ref_set(v___y_2639_, v___x_2678_);
v___x_2680_ = lean_box(0);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2680_);
v___x_2682_ = v___x_2645_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2689_, lean_object* v_msg_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2689_, v_msg_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
if (lean_obj_tag(v_as_2700_) == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
else
{
lean_object* v_options_2711_; uint8_t v_hasTrace_2712_; 
v_options_2711_ = lean_ctor_get(v___y_2706_, 2);
v_hasTrace_2712_ = lean_ctor_get_uint8(v_options_2711_, sizeof(void*)*1);
if (v_hasTrace_2712_ == 0)
{
lean_object* v_tail_2713_; 
v_tail_2713_ = lean_ctor_get(v_as_2700_, 1);
lean_inc(v_tail_2713_);
lean_dec_ref(v_as_2700_);
v_as_2700_ = v_tail_2713_;
goto _start;
}
else
{
lean_object* v_head_2715_; lean_object* v_tail_2716_; lean_object* v_fst_2717_; lean_object* v_snd_2718_; lean_object* v_inheritedTraceOptions_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_head_2715_ = lean_ctor_get(v_as_2700_, 0);
lean_inc(v_head_2715_);
v_tail_2716_ = lean_ctor_get(v_as_2700_, 1);
lean_inc(v_tail_2716_);
lean_dec_ref(v_as_2700_);
v_fst_2717_ = lean_ctor_get(v_head_2715_, 0);
lean_inc_n(v_fst_2717_, 2);
v_snd_2718_ = lean_ctor_get(v_head_2715_, 1);
lean_inc(v_snd_2718_);
lean_dec(v_head_2715_);
v_inheritedTraceOptions_2719_ = lean_ctor_get(v___y_2706_, 13);
v___x_2720_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2721_ = l_Lean_Name_append(v___x_2720_, v_fst_2717_);
v___x_2722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2719_, v_options_2711_, v___x_2721_);
lean_dec(v___x_2721_);
if (v___x_2722_ == 0)
{
lean_dec(v_snd_2718_);
lean_dec(v_fst_2717_);
v_as_2700_ = v_tail_2716_;
goto _start;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_snd_2718_);
v___x_2725_ = l_Lean_MessageData_ofFormat(v___x_2724_);
v___x_2726_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2717_, v___x_2725_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_dec_ref(v___x_2726_);
v_as_2700_ = v_tail_2716_;
goto _start;
}
else
{
lean_dec(v_tail_2716_);
return v___x_2726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2737_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(lean_object* v_keys_2738_, lean_object* v_i_2739_, lean_object* v_k_2740_){
_start:
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = lean_array_get_size(v_keys_2738_);
v___x_2742_ = lean_nat_dec_lt(v_i_2739_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_dec(v_i_2739_);
return v___x_2742_;
}
else
{
lean_object* v_k_x27_2743_; uint8_t v___x_2744_; 
v_k_x27_2743_ = lean_array_fget_borrowed(v_keys_2738_, v_i_2739_);
v___x_2744_ = l_Lean_instBEqExtraModUse_beq(v_k_2740_, v_k_x27_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_unsigned_to_nat(1u);
v___x_2746_ = lean_nat_add(v_i_2739_, v___x_2745_);
lean_dec(v_i_2739_);
v_i_2739_ = v___x_2746_;
goto _start;
}
else
{
lean_dec(v_i_2739_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg___boxed(lean_object* v_keys_2748_, lean_object* v_i_2749_, lean_object* v_k_2750_){
_start:
{
uint8_t v_res_2751_; lean_object* v_r_2752_; 
v_res_2751_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_keys_2748_, v_i_2749_, v_k_2750_);
lean_dec_ref(v_k_2750_);
lean_dec_ref(v_keys_2748_);
v_r_2752_ = lean_box(v_res_2751_);
return v_r_2752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2753_, size_t v_x_2754_, lean_object* v_x_2755_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
lean_object* v_es_2756_; lean_object* v___x_2757_; size_t v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; lean_object* v_j_2761_; lean_object* v___x_2762_; 
v_es_2756_ = lean_ctor_get(v_x_2753_, 0);
v___x_2757_ = lean_box(2);
v___x_2758_ = ((size_t)5ULL);
v___x_2759_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2760_ = lean_usize_land(v_x_2754_, v___x_2759_);
v_j_2761_ = lean_usize_to_nat(v___x_2760_);
v___x_2762_ = lean_array_get_borrowed(v___x_2757_, v_es_2756_, v_j_2761_);
lean_dec(v_j_2761_);
switch(lean_obj_tag(v___x_2762_))
{
case 0:
{
lean_object* v_key_2763_; uint8_t v___x_2764_; 
v_key_2763_ = lean_ctor_get(v___x_2762_, 0);
v___x_2764_ = l_Lean_instBEqExtraModUse_beq(v_x_2755_, v_key_2763_);
return v___x_2764_;
}
case 1:
{
lean_object* v_node_2765_; size_t v___x_2766_; 
v_node_2765_ = lean_ctor_get(v___x_2762_, 0);
v___x_2766_ = lean_usize_shift_right(v_x_2754_, v___x_2758_);
v_x_2753_ = v_node_2765_;
v_x_2754_ = v___x_2766_;
goto _start;
}
default: 
{
uint8_t v___x_2768_; 
v___x_2768_ = 0;
return v___x_2768_;
}
}
}
else
{
lean_object* v_ks_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_ks_2769_ = lean_ctor_get(v_x_2753_, 0);
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_ks_2769_, v___x_2770_, v_x_2755_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2772_, lean_object* v_x_2773_, lean_object* v_x_2774_){
_start:
{
size_t v_x_101121__boxed_2775_; uint8_t v_res_2776_; lean_object* v_r_2777_; 
v_x_101121__boxed_2775_ = lean_unbox_usize(v_x_2773_);
lean_dec(v_x_2773_);
v_res_2776_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2772_, v_x_101121__boxed_2775_, v_x_2774_);
lean_dec_ref(v_x_2774_);
lean_dec_ref(v_x_2772_);
v_r_2777_ = lean_box(v_res_2776_);
return v_r_2777_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
uint64_t v___x_2780_; size_t v___x_2781_; uint8_t v___x_2782_; 
v___x_2780_ = l_Lean_instHashableExtraModUse_hash(v_x_2779_);
v___x_2781_ = lean_uint64_to_usize(v___x_2780_);
v___x_2782_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2778_, v___x_2781_, v_x_2779_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2783_, v_x_2784_);
lean_dec_ref(v_x_2784_);
lean_dec_ref(v_x_2783_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2790_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2791_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2790_, v___x_2789_);
return v___x_2791_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
return v___x_2796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2798_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_ctor_set(v___x_2798_, 2, v___x_2797_);
lean_ctor_set(v___x_2798_, 3, v___x_2797_);
lean_ctor_set(v___x_2798_, 4, v___x_2797_);
lean_ctor_set(v___x_2798_, 5, v___x_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2804_ = l_Lean_stringToMessageData(v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2809_ = l_Lean_stringToMessageData(v___x_2808_);
return v___x_2809_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_cls_2810_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2811_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2812_ = l_Lean_Name_append(v___x_2811_, v_cls_2810_);
return v___x_2812_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2818_ = l_Lean_stringToMessageData(v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2823_, uint8_t v_isMeta_2824_, lean_object* v_hint_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_env_2835_; uint8_t v_isExporting_2836_; lean_object* v___x_2837_; lean_object* v_env_2838_; lean_object* v___x_2839_; lean_object* v_entry_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v___x_2834_ = lean_st_ref_get(v___y_2832_);
v_env_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_env_2835_);
lean_dec(v___x_2834_);
v_isExporting_2836_ = lean_ctor_get_uint8(v_env_2835_, sizeof(void*)*8);
lean_dec_ref(v_env_2835_);
v___x_2837_ = lean_st_ref_get(v___y_2832_);
v_env_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc_ref(v_env_2838_);
lean_dec(v___x_2837_);
v___x_2839_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2823_);
v_entry_2840_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2840_, 0, v_mod_2823_);
lean_ctor_set_uint8(v_entry_2840_, sizeof(void*)*1, v_isExporting_2836_);
lean_ctor_set_uint8(v_entry_2840_, sizeof(void*)*1 + 1, v_isMeta_2824_);
v___x_2841_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2842_ = lean_box(1);
v___x_2843_ = lean_box(0);
v___x_2887_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2839_, v___x_2841_, v_env_2838_, v___x_2842_, v___x_2843_);
v___x_2888_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2887_, v_entry_2840_);
lean_dec(v___x_2887_);
if (v___x_2888_ == 0)
{
lean_object* v_options_2889_; uint8_t v_hasTrace_2890_; 
v_options_2889_ = lean_ctor_get(v___y_2831_, 2);
v_hasTrace_2890_ = lean_ctor_get_uint8(v_options_2889_, sizeof(void*)*1);
if (v_hasTrace_2890_ == 0)
{
lean_dec(v_hint_2825_);
lean_dec(v_mod_2823_);
v___y_2845_ = v___y_2830_;
v___y_2846_ = v___y_2832_;
goto v___jp_2844_;
}
else
{
lean_object* v_inheritedTraceOptions_2891_; lean_object* v_cls_2892_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v_inheritedTraceOptions_2891_ = lean_ctor_get(v___y_2831_, 13);
v_cls_2892_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2912_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2891_, v_options_2889_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_dec(v_hint_2825_);
lean_dec(v_mod_2823_);
v___y_2845_ = v___y_2830_;
v___y_2846_ = v___y_2832_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2914_; lean_object* v___y_2916_; 
v___x_2914_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2836_ == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2916_ = v___x_2923_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2924_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2916_ = v___x_2924_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_inc_ref(v___y_2916_);
v___x_2917_ = l_Lean_stringToMessageData(v___y_2916_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2914_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
if (v_isMeta_2824_ == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2899_ = v___x_2920_;
v___y_2900_ = v___x_2921_;
goto v___jp_2898_;
}
else
{
lean_object* v___x_2922_; 
v___x_2922_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2899_ = v___x_2920_;
v___y_2900_ = v___x_2922_;
goto v___jp_2898_;
}
}
}
v___jp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___y_2894_);
lean_ctor_set(v___x_2896_, 1, v___y_2895_);
v___x_2897_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2892_, v___x_2896_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref(v___x_2897_);
v___y_2845_ = v___y_2830_;
v___y_2846_ = v___y_2832_;
goto v___jp_2844_;
}
else
{
lean_dec_ref(v_entry_2840_);
return v___x_2897_;
}
}
v___jp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
lean_inc_ref(v___y_2900_);
v___x_2901_ = l_Lean_stringToMessageData(v___y_2900_);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___y_2899_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = l_Lean_MessageData_ofName(v_mod_2823_);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_Name_isAnonymous(v_hint_2825_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2909_ = l_Lean_MessageData_ofName(v_hint_2825_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___y_2894_ = v___x_2906_;
v___y_2895_ = v___x_2910_;
goto v___jp_2893_;
}
else
{
lean_object* v___x_2911_; 
lean_dec(v_hint_2825_);
v___x_2911_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2894_ = v___x_2906_;
v___y_2895_ = v___x_2911_;
goto v___jp_2893_;
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v_entry_2840_);
lean_dec(v_hint_2825_);
lean_dec(v_mod_2823_);
v___x_2925_ = lean_box(0);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
v___jp_2844_:
{
lean_object* v___x_2847_; lean_object* v_toEnvExtension_2848_; lean_object* v_env_2849_; lean_object* v_nextMacroScope_2850_; lean_object* v_ngen_2851_; lean_object* v_auxDeclNGen_2852_; lean_object* v_traceState_2853_; lean_object* v_messages_2854_; lean_object* v_infoState_2855_; lean_object* v_snapshotTasks_2856_; lean_object* v_newDecls_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2885_; 
v___x_2847_ = lean_st_ref_take(v___y_2846_);
v_toEnvExtension_2848_ = lean_ctor_get(v___x_2841_, 0);
v_env_2849_ = lean_ctor_get(v___x_2847_, 0);
v_nextMacroScope_2850_ = lean_ctor_get(v___x_2847_, 1);
v_ngen_2851_ = lean_ctor_get(v___x_2847_, 2);
v_auxDeclNGen_2852_ = lean_ctor_get(v___x_2847_, 3);
v_traceState_2853_ = lean_ctor_get(v___x_2847_, 4);
v_messages_2854_ = lean_ctor_get(v___x_2847_, 6);
v_infoState_2855_ = lean_ctor_get(v___x_2847_, 7);
v_snapshotTasks_2856_ = lean_ctor_get(v___x_2847_, 8);
v_newDecls_2857_ = lean_ctor_get(v___x_2847_, 9);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v___x_2847_, 5);
lean_dec(v_unused_2886_);
v___x_2859_ = v___x_2847_;
v_isShared_2860_ = v_isSharedCheck_2885_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_newDecls_2857_);
lean_inc(v_snapshotTasks_2856_);
lean_inc(v_infoState_2855_);
lean_inc(v_messages_2854_);
lean_inc(v_traceState_2853_);
lean_inc(v_auxDeclNGen_2852_);
lean_inc(v_ngen_2851_);
lean_inc(v_nextMacroScope_2850_);
lean_inc(v_env_2849_);
lean_dec(v___x_2847_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2885_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_asyncMode_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v_asyncMode_2861_ = lean_ctor_get(v_toEnvExtension_2848_, 2);
v___x_2862_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2841_, v_env_2849_, v_entry_2840_, v_asyncMode_2861_, v___x_2843_);
v___x_2863_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 5, v___x_2863_);
lean_ctor_set(v___x_2859_, 0, v___x_2862_);
v___x_2865_ = v___x_2859_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_nextMacroScope_2850_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_ngen_2851_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_auxDeclNGen_2852_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_traceState_2853_);
lean_ctor_set(v_reuseFailAlloc_2884_, 5, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2884_, 6, v_messages_2854_);
lean_ctor_set(v_reuseFailAlloc_2884_, 7, v_infoState_2855_);
lean_ctor_set(v_reuseFailAlloc_2884_, 8, v_snapshotTasks_2856_);
lean_ctor_set(v_reuseFailAlloc_2884_, 9, v_newDecls_2857_);
v___x_2865_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_mctx_2868_; lean_object* v_zetaDeltaFVarIds_2869_; lean_object* v_postponed_2870_; lean_object* v_diag_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2882_; 
v___x_2866_ = lean_st_ref_set(v___y_2846_, v___x_2865_);
v___x_2867_ = lean_st_ref_take(v___y_2845_);
v_mctx_2868_ = lean_ctor_get(v___x_2867_, 0);
v_zetaDeltaFVarIds_2869_ = lean_ctor_get(v___x_2867_, 2);
v_postponed_2870_ = lean_ctor_get(v___x_2867_, 3);
v_diag_2871_ = lean_ctor_get(v___x_2867_, 4);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___x_2867_, 1);
lean_dec(v_unused_2883_);
v___x_2873_ = v___x_2867_;
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_diag_2871_);
lean_inc(v_postponed_2870_);
lean_inc(v_zetaDeltaFVarIds_2869_);
lean_inc(v_mctx_2868_);
lean_dec(v___x_2867_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2875_);
v___x_2877_ = v___x_2873_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_mctx_2868_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_zetaDeltaFVarIds_2869_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_postponed_2870_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_diag_2871_);
v___x_2877_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_st_ref_set(v___y_2845_, v___x_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2927_, lean_object* v_isMeta_2928_, lean_object* v_hint_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_isMeta_boxed_2938_; lean_object* v_res_2939_; 
v_isMeta_boxed_2938_ = lean_unbox(v_isMeta_2928_);
v_res_2939_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2927_, v_isMeta_boxed_2938_, v_hint_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2940_, lean_object* v_declName_2941_, lean_object* v_as_2942_, size_t v_sz_2943_, size_t v_i_2944_, lean_object* v_b_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
lean_dec(v_declName_2941_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_b_2945_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v_modules_2957_; lean_object* v___x_2958_; lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v_toImport_2961_; lean_object* v_module_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2956_ = l_Lean_Environment_header(v___x_2940_);
v_modules_2957_ = lean_ctor_get(v___x_2956_, 3);
lean_inc_ref(v_modules_2957_);
lean_dec_ref(v___x_2956_);
v___x_2958_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2959_ = lean_array_uget_borrowed(v_as_2942_, v_i_2944_);
v___x_2960_ = lean_array_get(v___x_2958_, v_modules_2957_, v_a_2959_);
lean_dec_ref(v_modules_2957_);
v_toImport_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc_ref(v_toImport_2961_);
lean_dec(v___x_2960_);
v_module_2962_ = lean_ctor_get(v_toImport_2961_, 0);
lean_inc(v_module_2962_);
lean_dec_ref(v_toImport_2961_);
v___x_2963_ = 0;
lean_inc(v_declName_2941_);
v___x_2964_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2962_, v___x_2963_, v_declName_2941_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; 
lean_dec_ref(v___x_2964_);
v___x_2965_ = lean_box(0);
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_add(v_i_2944_, v___x_2966_);
v_i_2944_ = v___x_2967_;
v_b_2945_ = v___x_2965_;
goto _start;
}
else
{
lean_dec(v_declName_2941_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2969_, lean_object* v_declName_2970_, lean_object* v_as_2971_, lean_object* v_sz_2972_, lean_object* v_i_2973_, lean_object* v_b_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
size_t v_sz_boxed_2983_; size_t v_i_boxed_2984_; lean_object* v_res_2985_; 
v_sz_boxed_2983_ = lean_unbox_usize(v_sz_2972_);
lean_dec(v_sz_2972_);
v_i_boxed_2984_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_res_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2969_, v_declName_2970_, v_as_2971_, v_sz_boxed_2983_, v_i_boxed_2984_, v_b_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v_as_2971_);
lean_dec_ref(v___x_2969_);
return v_res_2985_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2989_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2990_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2989_, v___x_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2993_, uint8_t v_isMeta_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v_env_3007_; lean_object* v___y_3009_; lean_object* v___x_3022_; 
v___x_3003_ = lean_st_ref_get(v___y_3001_);
v_env_3007_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_env_3007_);
lean_dec(v___x_3003_);
v___x_3022_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3007_, v_declName_2993_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec_ref(v_env_3007_);
lean_dec(v_declName_2993_);
goto v___jp_3004_;
}
else
{
lean_object* v_val_3023_; lean_object* v___x_3024_; lean_object* v_modules_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v_val_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3023_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = l_Lean_Environment_header(v_env_3007_);
v_modules_3025_ = lean_ctor_get(v___x_3024_, 3);
lean_inc_ref(v_modules_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = lean_array_get_size(v_modules_3025_);
v___x_3027_ = lean_nat_dec_lt(v_val_3023_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_dec_ref(v_modules_3025_);
lean_dec(v_val_3023_);
lean_dec_ref(v_env_3007_);
lean_dec(v_declName_2993_);
goto v___jp_3004_;
}
else
{
lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___y_3033_; 
v___x_3028_ = lean_st_ref_get(v___y_3001_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3029_);
lean_dec(v___x_3028_);
v___x_3030_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_3031_ = lean_array_fget(v_modules_3025_, v_val_3023_);
lean_dec(v_val_3023_);
lean_dec_ref(v_modules_3025_);
if (v_isMeta_2994_ == 0)
{
lean_dec_ref(v_env_3029_);
v___y_3033_ = v_isMeta_2994_;
goto v___jp_3032_;
}
else
{
uint8_t v___x_3044_; 
lean_inc(v_declName_2993_);
v___x_3044_ = l_Lean_isMarkedMeta(v_env_3029_, v_declName_2993_);
if (v___x_3044_ == 0)
{
v___y_3033_ = v_isMeta_2994_;
goto v___jp_3032_;
}
else
{
uint8_t v___x_3045_; 
v___x_3045_ = 0;
v___y_3033_ = v___x_3045_;
goto v___jp_3032_;
}
}
v___jp_3032_:
{
lean_object* v_toImport_3034_; lean_object* v_module_3035_; lean_object* v___x_3036_; 
v_toImport_3034_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_ref(v_toImport_3034_);
lean_dec(v___x_3031_);
v_module_3035_ = lean_ctor_get(v_toImport_3034_, 0);
lean_inc(v_module_3035_);
lean_dec_ref(v_toImport_3034_);
lean_inc(v_declName_2993_);
v___x_3036_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_3035_, v___y_3033_, v_declName_2993_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v___x_3036_);
v___x_3037_ = l_Lean_indirectModUseExt;
v___x_3038_ = lean_box(1);
v___x_3039_ = lean_box(0);
lean_inc_ref(v_env_3007_);
v___x_3040_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3030_, v___x_3037_, v_env_3007_, v___x_3038_, v___x_3039_);
v___x_3041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___redArg(v___x_3040_, v_declName_2993_);
lean_dec(v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_3009_ = v___x_3042_;
goto v___jp_3008_;
}
else
{
lean_object* v_val_3043_; 
v_val_3043_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_val_3043_);
lean_dec_ref(v___x_3041_);
v___y_3009_ = v_val_3043_;
goto v___jp_3008_;
}
}
else
{
lean_dec_ref(v_env_3007_);
lean_dec(v_declName_2993_);
return v___x_3036_;
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
v___jp_3008_:
{
lean_object* v___x_3010_; size_t v_sz_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3010_ = lean_box(0);
v_sz_3011_ = lean_array_size(v___y_3009_);
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_3007_, v_declName_2993_, v___y_3009_, v_sz_3011_, v___x_3012_, v___x_3010_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_env_3007_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v___x_3013_, 0);
lean_dec(v_unused_3021_);
v___x_3015_ = v___x_3013_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v___x_3013_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3010_);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3010_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_3046_, lean_object* v_isMeta_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v_isMeta_boxed_3056_; lean_object* v_res_3057_; 
v_isMeta_boxed_3056_ = lean_unbox(v_isMeta_3047_);
v_res_3057_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_3046_, v_isMeta_boxed_3056_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_3058_, lean_object* v_b_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
if (lean_obj_tag(v_as_x27_3058_) == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_b_3059_);
return v___x_3068_;
}
else
{
lean_object* v_head_3069_; lean_object* v_tail_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; 
v_head_3069_ = lean_ctor_get(v_as_x27_3058_, 0);
v_tail_3070_ = lean_ctor_get(v_as_x27_3058_, 1);
v___x_3071_ = 1;
lean_inc(v_head_3069_);
v___x_3072_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_3069_, v___x_3071_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v___x_3073_; 
lean_dec_ref(v___x_3072_);
v___x_3073_ = lean_box(0);
v_as_x27_3058_ = v_tail_3070_;
v_b_3059_ = v___x_3073_;
goto _start;
}
else
{
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_3075_, lean_object* v_b_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3075_, v_b_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v_as_x27_3075_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_3086_, lean_object* v_options_3087_, lean_object* v_currNamespace_3088_, lean_object* v_openDecls_3089_, lean_object* v_n_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = l_Lean_ResolveName_resolveGlobalName(v_env_3086_, v_options_3087_, v_currNamespace_3088_, v_openDecls_3089_, v_n_3090_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___y_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_3095_, lean_object* v_options_3096_, lean_object* v_currNamespace_3097_, lean_object* v_openDecls_3098_, lean_object* v_n_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_3095_, v_options_3096_, v_currNamespace_3097_, v_openDecls_3098_, v_n_3099_, v___y_3100_, v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v_options_3096_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_fileName_3110_; lean_object* v_fileMap_3111_; lean_object* v_options_3112_; lean_object* v_currRecDepth_3113_; lean_object* v_maxRecDepth_3114_; lean_object* v_ref_3115_; lean_object* v_currNamespace_3116_; lean_object* v_openDecls_3117_; lean_object* v_initHeartbeats_3118_; lean_object* v_maxHeartbeats_3119_; lean_object* v_quotContext_3120_; lean_object* v_currMacroScope_3121_; uint8_t v_diag_3122_; lean_object* v_cancelTk_x3f_3123_; uint8_t v_suppressElabErrors_3124_; lean_object* v_inheritedTraceOptions_3125_; lean_object* v_ref_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_fileName_3110_ = lean_ctor_get(v___y_3107_, 0);
v_fileMap_3111_ = lean_ctor_get(v___y_3107_, 1);
v_options_3112_ = lean_ctor_get(v___y_3107_, 2);
v_currRecDepth_3113_ = lean_ctor_get(v___y_3107_, 3);
v_maxRecDepth_3114_ = lean_ctor_get(v___y_3107_, 4);
v_ref_3115_ = lean_ctor_get(v___y_3107_, 5);
v_currNamespace_3116_ = lean_ctor_get(v___y_3107_, 6);
v_openDecls_3117_ = lean_ctor_get(v___y_3107_, 7);
v_initHeartbeats_3118_ = lean_ctor_get(v___y_3107_, 8);
v_maxHeartbeats_3119_ = lean_ctor_get(v___y_3107_, 9);
v_quotContext_3120_ = lean_ctor_get(v___y_3107_, 10);
v_currMacroScope_3121_ = lean_ctor_get(v___y_3107_, 11);
v_diag_3122_ = lean_ctor_get_uint8(v___y_3107_, sizeof(void*)*14);
v_cancelTk_x3f_3123_ = lean_ctor_get(v___y_3107_, 12);
v_suppressElabErrors_3124_ = lean_ctor_get_uint8(v___y_3107_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3125_ = lean_ctor_get(v___y_3107_, 13);
v_ref_3126_ = l_Lean_replaceRef(v_ref_3103_, v_ref_3115_);
lean_inc_ref(v_inheritedTraceOptions_3125_);
lean_inc(v_cancelTk_x3f_3123_);
lean_inc(v_currMacroScope_3121_);
lean_inc(v_quotContext_3120_);
lean_inc(v_maxHeartbeats_3119_);
lean_inc(v_initHeartbeats_3118_);
lean_inc(v_openDecls_3117_);
lean_inc(v_currNamespace_3116_);
lean_inc(v_maxRecDepth_3114_);
lean_inc(v_currRecDepth_3113_);
lean_inc_ref(v_options_3112_);
lean_inc_ref(v_fileMap_3111_);
lean_inc_ref(v_fileName_3110_);
v___x_3127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3127_, 0, v_fileName_3110_);
lean_ctor_set(v___x_3127_, 1, v_fileMap_3111_);
lean_ctor_set(v___x_3127_, 2, v_options_3112_);
lean_ctor_set(v___x_3127_, 3, v_currRecDepth_3113_);
lean_ctor_set(v___x_3127_, 4, v_maxRecDepth_3114_);
lean_ctor_set(v___x_3127_, 5, v_ref_3126_);
lean_ctor_set(v___x_3127_, 6, v_currNamespace_3116_);
lean_ctor_set(v___x_3127_, 7, v_openDecls_3117_);
lean_ctor_set(v___x_3127_, 8, v_initHeartbeats_3118_);
lean_ctor_set(v___x_3127_, 9, v_maxHeartbeats_3119_);
lean_ctor_set(v___x_3127_, 10, v_quotContext_3120_);
lean_ctor_set(v___x_3127_, 11, v_currMacroScope_3121_);
lean_ctor_set(v___x_3127_, 12, v_cancelTk_x3f_3123_);
lean_ctor_set(v___x_3127_, 13, v_inheritedTraceOptions_3125_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*14, v_diag_3122_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*14 + 1, v_suppressElabErrors_3124_);
v___x_3128_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_3104_, v___y_3105_, v___y_3106_, v___x_3127_, v___y_3108_);
lean_dec_ref(v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_3129_, lean_object* v_msg_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3129_, v_msg_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v_ref_3129_);
return v_res_3136_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = l_Lean_maxRecDepthErrorMessage;
v___x_3143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_3145_ = l_Lean_MessageData_ofFormat(v___x_3144_);
return v___x_3145_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3147_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3148_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3149_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_ref_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; lean_object* v_env_3168_; lean_object* v_options_3169_; lean_object* v_currRecDepth_3170_; lean_object* v_maxRecDepth_3171_; lean_object* v_ref_3172_; lean_object* v_currNamespace_3173_; lean_object* v_openDecls_3174_; lean_object* v_quotContext_3175_; lean_object* v_currMacroScope_3176_; lean_object* v___x_3177_; lean_object* v_nextMacroScope_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___f_3182_; lean_object* v___f_3183_; lean_object* v_methods_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3167_ = lean_st_ref_get(v___y_3165_);
v_env_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc_ref_n(v_env_3168_, 4);
lean_dec(v___x_3167_);
v_options_3169_ = lean_ctor_get(v___y_3164_, 2);
v_currRecDepth_3170_ = lean_ctor_get(v___y_3164_, 3);
v_maxRecDepth_3171_ = lean_ctor_get(v___y_3164_, 4);
v_ref_3172_ = lean_ctor_get(v___y_3164_, 5);
v_currNamespace_3173_ = lean_ctor_get(v___y_3164_, 6);
v_openDecls_3174_ = lean_ctor_get(v___y_3164_, 7);
v_quotContext_3175_ = lean_ctor_get(v___y_3164_, 10);
v_currMacroScope_3176_ = lean_ctor_get(v___y_3164_, 11);
v___x_3177_ = lean_st_ref_get(v___y_3165_);
v_nextMacroScope_3178_ = lean_ctor_get(v___x_3177_, 1);
lean_inc(v_nextMacroScope_3178_);
lean_dec(v___x_3177_);
v___f_3179_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3179_, 0, v_env_3168_);
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3180_, 0, v_env_3168_);
lean_inc_n(v_openDecls_3174_, 2);
lean_inc_n(v_currNamespace_3173_, 3);
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3181_, 0, v_env_3168_);
lean_closure_set(v___f_3181_, 1, v_currNamespace_3173_);
lean_closure_set(v___f_3181_, 2, v_openDecls_3174_);
v___f_3182_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3182_, 0, v_currNamespace_3173_);
lean_inc_ref(v_options_3169_);
v___f_3183_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3183_, 0, v_env_3168_);
lean_closure_set(v___f_3183_, 1, v_options_3169_);
lean_closure_set(v___f_3183_, 2, v_currNamespace_3173_);
lean_closure_set(v___f_3183_, 3, v_openDecls_3174_);
v_methods_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3184_, 0, v___f_3179_);
lean_ctor_set(v_methods_3184_, 1, v___f_3182_);
lean_ctor_set(v_methods_3184_, 2, v___f_3180_);
lean_ctor_set(v_methods_3184_, 3, v___f_3181_);
lean_ctor_set(v_methods_3184_, 4, v___f_3183_);
lean_inc(v_ref_3172_);
lean_inc(v_maxRecDepth_3171_);
lean_inc(v_currRecDepth_3170_);
lean_inc(v_currMacroScope_3176_);
lean_inc(v_quotContext_3175_);
v___x_3185_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3185_, 0, v_methods_3184_);
lean_ctor_set(v___x_3185_, 1, v_quotContext_3175_);
lean_ctor_set(v___x_3185_, 2, v_currMacroScope_3176_);
lean_ctor_set(v___x_3185_, 3, v_currRecDepth_3170_);
lean_ctor_set(v___x_3185_, 4, v_maxRecDepth_3171_);
lean_ctor_set(v___x_3185_, 5, v_ref_3172_);
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3187_, 0, v_nextMacroScope_3178_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
lean_ctor_set(v___x_3187_, 2, v___x_3186_);
v___x_3188_ = lean_apply_2(v_x_3158_, v___x_3185_, v___x_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v_a_3190_; lean_object* v_macroScope_3191_; lean_object* v_traceMsgs_3192_; lean_object* v_expandedMacroDecls_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_a_3189_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3190_);
lean_dec_ref(v___x_3188_);
v_macroScope_3191_ = lean_ctor_get(v_a_3189_, 0);
lean_inc(v_macroScope_3191_);
v_traceMsgs_3192_ = lean_ctor_get(v_a_3189_, 1);
lean_inc(v_traceMsgs_3192_);
v_expandedMacroDecls_3193_ = lean_ctor_get(v_a_3189_, 2);
lean_inc(v_expandedMacroDecls_3193_);
lean_dec(v_a_3189_);
v___x_3194_ = lean_box(0);
v___x_3195_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3193_, v___x_3194_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v_expandedMacroDecls_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v___x_3196_; lean_object* v_env_3197_; lean_object* v_ngen_3198_; lean_object* v_auxDeclNGen_3199_; lean_object* v_traceState_3200_; lean_object* v_cache_3201_; lean_object* v_messages_3202_; lean_object* v_infoState_3203_; lean_object* v_snapshotTasks_3204_; lean_object* v_newDecls_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_3195_);
v___x_3196_ = lean_st_ref_take(v___y_3165_);
v_env_3197_ = lean_ctor_get(v___x_3196_, 0);
v_ngen_3198_ = lean_ctor_get(v___x_3196_, 2);
v_auxDeclNGen_3199_ = lean_ctor_get(v___x_3196_, 3);
v_traceState_3200_ = lean_ctor_get(v___x_3196_, 4);
v_cache_3201_ = lean_ctor_get(v___x_3196_, 5);
v_messages_3202_ = lean_ctor_get(v___x_3196_, 6);
v_infoState_3203_ = lean_ctor_get(v___x_3196_, 7);
v_snapshotTasks_3204_ = lean_ctor_get(v___x_3196_, 8);
v_newDecls_3205_ = lean_ctor_get(v___x_3196_, 9);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3196_, 1);
lean_dec(v_unused_3232_);
v___x_3207_ = v___x_3196_;
v_isShared_3208_ = v_isSharedCheck_3231_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_newDecls_3205_);
lean_inc(v_snapshotTasks_3204_);
lean_inc(v_infoState_3203_);
lean_inc(v_messages_3202_);
lean_inc(v_cache_3201_);
lean_inc(v_traceState_3200_);
lean_inc(v_auxDeclNGen_3199_);
lean_inc(v_ngen_3198_);
lean_inc(v_env_3197_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3231_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v_macroScope_3191_);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_env_3197_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_macroScope_3191_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_ngen_3198_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_auxDeclNGen_3199_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v_traceState_3200_);
lean_ctor_set(v_reuseFailAlloc_3230_, 5, v_cache_3201_);
lean_ctor_set(v_reuseFailAlloc_3230_, 6, v_messages_3202_);
lean_ctor_set(v_reuseFailAlloc_3230_, 7, v_infoState_3203_);
lean_ctor_set(v_reuseFailAlloc_3230_, 8, v_snapshotTasks_3204_);
lean_ctor_set(v_reuseFailAlloc_3230_, 9, v_newDecls_3205_);
v___x_3210_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_st_ref_set(v___y_3165_, v___x_3210_);
v___x_3212_ = l_List_reverse___redArg(v_traceMsgs_3192_);
v___x_3213_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3212_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3221_);
v___x_3215_ = v___x_3213_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v___x_3213_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v_a_3190_);
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3190_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_a_3190_);
v_a_3222_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3213_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3213_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec(v_traceMsgs_3192_);
lean_dec(v_macroScope_3191_);
lean_dec(v_a_3190_);
v_a_3233_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3195_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3195_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3241_; 
v_a_3241_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3188_);
if (lean_obj_tag(v_a_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v_a_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_a_3242_ = lean_ctor_get(v_a_3241_, 0);
lean_inc(v_a_3242_);
v_a_3243_ = lean_ctor_get(v_a_3241_, 1);
lean_inc_ref(v_a_3243_);
lean_dec_ref(v_a_3241_);
v___x_3244_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3245_ = lean_string_dec_eq(v_a_3243_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3243_);
v___x_3247_ = l_Lean_MessageData_ofFormat(v___x_3246_);
v___x_3248_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3242_, v___x_3247_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v_a_3242_);
return v___x_3248_;
}
else
{
lean_object* v___x_3249_; 
lean_dec_ref(v_a_3243_);
v___x_3249_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3242_);
return v___x_3249_;
}
}
else
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_quotContext_3265_; lean_object* v_currMacroScope_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_quotContext_3265_ = lean_ctor_get(v___y_3262_, 10);
lean_inc(v_quotContext_3265_);
v_currMacroScope_3266_ = lean_ctor_get(v___y_3262_, 11);
lean_inc(v_currMacroScope_3266_);
lean_dec_ref(v___y_3262_);
v___x_3267_ = l_Lean_addMacroScope(v_quotContext_3265_, v___x_3261_, v_currMacroScope_3266_);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___f_3282_; lean_object* v___x_3283_; 
v___f_3282_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3283_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3282_, v___y_3279_, v___y_3280_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3288_, uint8_t v_canonical_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3307_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = l_Lean_mkIdentFrom(v_ref_3288_, v_a_3299_, v_canonical_3289_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3303_);
v___x_3305_ = v___x_3301_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_a_3308_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3298_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3298_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3316_, lean_object* v_canonical_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v_canonical_boxed_3326_; lean_object* v_res_3327_; 
v_canonical_boxed_3326_ = lean_unbox(v_canonical_3317_);
v_res_3327_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3316_, v_canonical_boxed_3326_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v_ref_3316_);
return v_res_3327_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3340_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3341_ = l_Lean_Name_append(v___x_3340_, v___x_3339_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3344_ = l_Lean_stringToMessageData(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3351_, lean_object* v_letOrReassign_3352_, lean_object* v_decl_3353_, lean_object* v_tk_3354_, lean_object* v_dec_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3351_, v_letOrReassign_3352_, v_decl_3353_, v_tk_3354_, v_dec_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec_ref(v_a_3356_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3365_, lean_object* v_letOrReassign_3366_, lean_object* v_decl_3367_, lean_object* v_tk_3368_, lean_object* v_dec_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3365_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v___x_3379_; 
lean_dec_ref(v___x_3378_);
lean_inc(v_decl_3367_);
v___x_3379_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3367_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref(v___x_3379_);
v___x_3381_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3366_, v_a_3380_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3382_; 
lean_dec_ref(v___x_3381_);
v___x_3382_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3369_, v_tk_3368_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3366_, v_decl_3367_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v_doBlockResultType_3386_; lean_object* v___x_3387_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
v_doBlockResultType_3386_ = lean_ctor_get(v_a_3370_, 3);
lean_inc_ref(v_doBlockResultType_3386_);
v___x_3387_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_3386_, v_a_3370_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3606_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3606_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3606_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3393_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3394_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3395_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3385_);
v___x_3396_ = l_Lean_Syntax_isOfKind(v_a_3385_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3385_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_tk_3368_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v___x_3397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = l_Lean_Syntax_getArg(v_a_3385_, v___x_3398_);
lean_dec(v_a_3385_);
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3399_);
v___x_3401_ = l_Lean_Syntax_isOfKind(v___x_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
lean_dec(v_tk_3368_);
v___x_3402_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3399_);
v___x_3403_ = l_Lean_Syntax_isOfKind(v___x_3399_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; uint8_t v___x_3405_; 
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3399_);
v___x_3405_ = l_Lean_Syntax_isOfKind(v___x_3399_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec(v___x_3399_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v___x_3406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; lean_object* v_id_3408_; lean_object* v_binders_3409_; lean_object* v_type_3410_; lean_object* v_value_3411_; lean_object* v___y_3413_; uint8_t v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; uint8_t v___y_3425_; lean_object* v_id_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; uint8_t v___x_3502_; 
v___x_3407_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3399_);
lean_dec(v___x_3399_);
v_id_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_id_3408_);
v_binders_3409_ = lean_ctor_get(v___x_3407_, 1);
lean_inc_ref(v_binders_3409_);
v_type_3410_ = lean_ctor_get(v___x_3407_, 2);
lean_inc(v_type_3410_);
v_value_3411_ = lean_ctor_get(v___x_3407_, 3);
lean_inc(v_value_3411_);
lean_dec_ref(v___x_3407_);
v___x_3502_ = l_Lean_Syntax_isIdent(v_id_3408_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3408_, v___x_3396_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec(v_id_3408_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v_id_3484_ = v_a_3504_;
v___y_3485_ = v_a_3370_;
v___y_3486_ = v_a_3371_;
v___y_3487_ = v_a_3372_;
v___y_3488_ = v_a_3373_;
v___y_3489_ = v_a_3374_;
v___y_3490_ = v_a_3375_;
v___y_3491_ = v_a_3376_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_value_3411_);
lean_dec(v_type_3410_);
lean_dec_ref(v_binders_3409_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
v_id_3484_ = v_id_3408_;
v___y_3485_ = v_a_3370_;
v___y_3486_ = v_a_3371_;
v___y_3487_ = v_a_3372_;
v___y_3488_ = v_a_3373_;
v___y_3489_ = v_a_3374_;
v___y_3490_ = v_a_3375_;
v___y_3491_ = v_a_3376_;
goto v___jp_3483_;
}
v___jp_3412_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; 
v___x_3426_ = lean_box(v___x_3396_);
v___x_3427_ = lean_box(v___x_3401_);
v___x_3428_ = lean_box(v___y_3425_);
v___f_3429_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3429_, 0, v_type_3410_);
lean_closure_set(v___f_3429_, 1, v_value_3411_);
lean_closure_set(v___f_3429_, 2, v___x_3426_);
lean_closure_set(v___f_3429_, 3, v___x_3427_);
lean_closure_set(v___f_3429_, 4, v___x_3398_);
lean_closure_set(v___f_3429_, 5, v___x_3428_);
v___x_3430_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3409_, v___f_3429_, v___y_3423_, v___y_3420_, v___y_3417_, v___y_3424_, v___y_3419_, v___y_3422_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v_options_3432_; lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3474_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
v_options_3432_ = lean_ctor_get(v___y_3419_, 2);
v_fst_3433_ = lean_ctor_get(v_a_3431_, 0);
v_snd_3434_ = lean_ctor_get(v_a_3431_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_a_3431_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3436_ = v_a_3431_;
v_isShared_3437_ = v_isSharedCheck_3474_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_inc(v_fst_3433_);
lean_dec(v_a_3431_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3474_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_inheritedTraceOptions_3438_; uint8_t v_hasTrace_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_inheritedTraceOptions_3438_ = lean_ctor_get(v___y_3419_, 13);
v_hasTrace_3439_ = lean_ctor_get_uint8(v_options_3432_, sizeof(void*)*1);
v___x_3440_ = lean_box(v___y_3414_);
v___x_3441_ = lean_box(v___y_3416_);
v___x_3442_ = lean_box(v___x_3401_);
v___x_3443_ = lean_box(v___y_3425_);
v___x_3444_ = lean_box(v___x_3396_);
lean_inc(v_snd_3434_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3445_, 0, v___y_3413_);
lean_closure_set(v___f_3445_, 1, v___y_3415_);
lean_closure_set(v___f_3445_, 2, v_a_3383_);
lean_closure_set(v___f_3445_, 3, v___x_3440_);
lean_closure_set(v___f_3445_, 4, v___x_3441_);
lean_closure_set(v___f_3445_, 5, v___x_3442_);
lean_closure_set(v___f_3445_, 6, v_snd_3434_);
lean_closure_set(v___f_3445_, 7, v___x_3443_);
lean_closure_set(v___f_3445_, 8, v___x_3444_);
lean_closure_set(v___f_3445_, 9, v_letOrReassign_3366_);
lean_closure_set(v___f_3445_, 10, v_a_3380_);
v___x_3446_ = l_Lean_Syntax_getId(v___y_3418_);
lean_dec(v___y_3418_);
v___x_3447_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3446_);
if (v_hasTrace_3439_ == 0)
{
lean_object* v___x_3448_; 
lean_del_object(v___x_3436_);
v___x_3448_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3446_, v_fst_3433_, v_snd_3434_, v___f_3445_, v___y_3425_, v___x_3447_, v___y_3421_, v___y_3423_, v___y_3420_, v___y_3417_, v___y_3424_, v___y_3419_, v___y_3422_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3449_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3450_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3438_, v_options_3432_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_del_object(v___x_3436_);
v___x_3452_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3446_, v_fst_3433_, v_snd_3434_, v___f_3445_, v___y_3425_, v___x_3447_, v___y_3421_, v___y_3423_, v___y_3420_, v___y_3417_, v___y_3424_, v___y_3419_, v___y_3422_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_inc(v___x_3446_);
v___x_3453_ = l_Lean_MessageData_ofName(v___x_3446_);
v___x_3454_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 7);
lean_ctor_set(v___x_3436_, 1, v___x_3454_);
lean_ctor_set(v___x_3436_, 0, v___x_3453_);
v___x_3456_ = v___x_3436_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_inc(v_fst_3433_);
v___x_3457_ = l_Lean_MessageData_ofExpr(v_fst_3433_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
lean_inc(v_snd_3434_);
v___x_3461_ = l_Lean_MessageData_ofExpr(v_snd_3434_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3449_, v___x_3462_, v___y_3417_, v___y_3424_, v___y_3419_, v___y_3422_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v___x_3463_);
v___x_3464_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3446_, v_fst_3433_, v_snd_3434_, v___f_3445_, v___y_3425_, v___x_3447_, v___y_3421_, v___y_3423_, v___y_3420_, v___y_3417_, v___y_3424_, v___y_3419_, v___y_3422_);
return v___x_3464_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v___x_3446_);
lean_dec_ref(v___f_3445_);
lean_dec(v_snd_3434_);
lean_dec(v_fst_3433_);
v_a_3465_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3463_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
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
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v___y_3418_);
lean_dec(v___y_3415_);
lean_dec(v___y_3413_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
v_a_3475_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3430_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3430_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v___jp_3483_:
{
uint8_t v_nondep_3492_; 
v_nondep_3492_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1);
if (v_nondep_3492_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3366_) == 1)
{
uint8_t v_usedOnly_3493_; uint8_t v_zeta_3494_; lean_object* v_eq_x3f_3495_; 
v_usedOnly_3493_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 1);
v_zeta_3494_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 2);
v_eq_x3f_3495_ = lean_ctor_get(v_config_3365_, 0);
lean_inc(v_eq_x3f_3495_);
lean_dec_ref(v_config_3365_);
lean_inc(v_id_3484_);
v___y_3413_ = v_id_3484_;
v___y_3414_ = v_zeta_3494_;
v___y_3415_ = v_eq_x3f_3495_;
v___y_3416_ = v_usedOnly_3493_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v_id_3484_;
v___y_3419_ = v___y_3490_;
v___y_3420_ = v___y_3487_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3491_;
v___y_3423_ = v___y_3486_;
v___y_3424_ = v___y_3489_;
v___y_3425_ = v___x_3396_;
goto v___jp_3412_;
}
else
{
uint8_t v_usedOnly_3496_; uint8_t v_zeta_3497_; lean_object* v_eq_x3f_3498_; 
v_usedOnly_3496_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 1);
v_zeta_3497_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 2);
v_eq_x3f_3498_ = lean_ctor_get(v_config_3365_, 0);
lean_inc(v_eq_x3f_3498_);
lean_dec_ref(v_config_3365_);
lean_inc(v_id_3484_);
v___y_3413_ = v_id_3484_;
v___y_3414_ = v_zeta_3497_;
v___y_3415_ = v_eq_x3f_3498_;
v___y_3416_ = v_usedOnly_3496_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v_id_3484_;
v___y_3419_ = v___y_3490_;
v___y_3420_ = v___y_3487_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3491_;
v___y_3423_ = v___y_3486_;
v___y_3424_ = v___y_3489_;
v___y_3425_ = v_nondep_3492_;
goto v___jp_3412_;
}
}
else
{
uint8_t v_usedOnly_3499_; uint8_t v_zeta_3500_; lean_object* v_eq_x3f_3501_; 
v_usedOnly_3499_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 1);
v_zeta_3500_ = lean_ctor_get_uint8(v_config_3365_, sizeof(void*)*1 + 2);
v_eq_x3f_3501_ = lean_ctor_get(v_config_3365_, 0);
lean_inc(v_eq_x3f_3501_);
lean_dec_ref(v_config_3365_);
lean_inc(v_id_3484_);
v___y_3413_ = v_id_3484_;
v___y_3414_ = v_zeta_3500_;
v___y_3415_ = v_eq_x3f_3501_;
v___y_3416_ = v_usedOnly_3499_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v_id_3484_;
v___y_3419_ = v___y_3490_;
v___y_3420_ = v___y_3487_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3491_;
v___y_3423_ = v___y_3486_;
v___y_3424_ = v___y_3489_;
v___y_3425_ = v___x_3396_;
goto v___jp_3412_;
}
}
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = l_Lean_Syntax_getArg(v___x_3399_, v___x_3513_);
v___x_3515_ = l_Lean_Syntax_matchesNull(v___x_3514_, v___x_3398_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v___x_3399_);
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v___x_3516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3516_;
}
else
{
lean_object* v___x_3517_; lean_object* v___f_3518_; lean_object* v___x_3519_; lean_object* v_rhs_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v_xType_x3f_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3517_ = lean_box(v___x_3401_);
v___f_3518_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3518_, 0, v___x_3517_);
v___x_3519_ = l_Lean_Syntax_getArg(v___x_3399_, v___x_3398_);
v___x_3574_ = lean_unsigned_to_nat(2u);
v___x_3575_ = l_Lean_Syntax_getArg(v___x_3399_, v___x_3574_);
v___x_3576_ = l_Lean_Syntax_isNone(v___x_3575_);
if (v___x_3576_ == 0)
{
uint8_t v___x_3577_; 
lean_inc(v___x_3575_);
v___x_3577_ = l_Lean_Syntax_matchesNull(v___x_3575_, v___x_3513_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; 
lean_dec(v___x_3575_);
lean_dec(v___x_3519_);
lean_dec_ref(v___f_3518_);
lean_dec(v___x_3399_);
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v___x_3578_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3578_;
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = l_Lean_Syntax_getArg(v___x_3575_, v___x_3398_);
lean_dec(v___x_3575_);
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3579_);
v___x_3581_ = l_Lean_Syntax_isOfKind(v___x_3579_, v___x_3580_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
lean_dec(v___x_3579_);
lean_dec(v___x_3519_);
lean_dec_ref(v___f_3518_);
lean_dec(v___x_3399_);
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v___x_3582_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3582_;
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = l_Lean_Syntax_getArg(v___x_3579_, v___x_3513_);
lean_dec(v___x_3579_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 1);
lean_ctor_set(v___x_3390_, 0, v___x_3583_);
v___x_3585_ = v___x_3390_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
v_xType_x3f_3540_ = v___x_3585_;
v___y_3541_ = v_a_3370_;
v___y_3542_ = v_a_3371_;
v___y_3543_ = v_a_3372_;
v___y_3544_ = v_a_3373_;
v___y_3545_ = v_a_3374_;
v___y_3546_ = v_a_3375_;
v___y_3547_ = v_a_3376_;
goto v___jp_3539_;
}
}
}
}
else
{
lean_object* v___x_3587_; 
lean_dec(v___x_3575_);
lean_del_object(v___x_3390_);
v___x_3587_ = lean_box(0);
v_xType_x3f_3540_ = v___x_3587_;
v___y_3541_ = v_a_3370_;
v___y_3542_ = v_a_3371_;
v___y_3543_ = v_a_3372_;
v___y_3544_ = v_a_3373_;
v___y_3545_ = v_a_3374_;
v___y_3546_ = v_a_3375_;
v___y_3547_ = v_a_3376_;
goto v___jp_3539_;
}
v___jp_3520_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___f_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3529_ = lean_box(v___x_3401_);
v___x_3530_ = lean_box(v___x_3396_);
lean_inc(v___x_3519_);
v___f_3531_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3531_, 0, v_rhs_3521_);
lean_closure_set(v___f_3531_, 1, v___x_3529_);
lean_closure_set(v___f_3531_, 2, v_config_3365_);
lean_closure_set(v___f_3531_, 3, v_a_3388_);
lean_closure_set(v___f_3531_, 4, v___x_3530_);
lean_closure_set(v___f_3531_, 5, v___x_3392_);
lean_closure_set(v___f_3531_, 6, v___x_3393_);
lean_closure_set(v___f_3531_, 7, v___x_3394_);
lean_closure_set(v___f_3531_, 8, v___f_3518_);
lean_closure_set(v___f_3531_, 9, v___x_3519_);
v___x_3532_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3532_, 0, v_a_3383_);
v___x_3533_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3533_, 0, v_letOrReassign_3366_);
lean_closure_set(v___x_3533_, 1, v_a_3380_);
lean_closure_set(v___x_3533_, 2, v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3535_ = l_Lean_MessageData_ofSyntax(v___x_3519_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_box(0);
v___x_3538_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3536_, v___x_3533_, v___f_3531_, v___x_3537_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
return v___x_3538_;
}
v___jp_3539_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_unsigned_to_nat(4u);
v___x_3549_ = l_Lean_Syntax_getArg(v___x_3399_, v___x_3548_);
lean_dec(v___x_3399_);
if (lean_obj_tag(v_xType_x3f_3540_) == 0)
{
v_rhs_3521_ = v___x_3549_;
v___y_3522_ = v___y_3541_;
v___y_3523_ = v___y_3542_;
v___y_3524_ = v___y_3543_;
v___y_3525_ = v___y_3544_;
v___y_3526_ = v___y_3545_;
v___y_3527_ = v___y_3546_;
v___y_3528_ = v___y_3547_;
goto v___jp_3520_;
}
else
{
lean_object* v_val_3550_; lean_object* v_ref_3551_; lean_object* v_quotContext_3552_; lean_object* v_currMacroScope_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_val_3550_ = lean_ctor_get(v_xType_x3f_3540_, 0);
lean_inc(v_val_3550_);
lean_dec_ref(v_xType_x3f_3540_);
v_ref_3551_ = lean_ctor_get(v___y_3546_, 5);
v_quotContext_3552_ = lean_ctor_get(v___y_3546_, 10);
v_currMacroScope_3553_ = lean_ctor_get(v___y_3546_, 11);
v___x_3554_ = l_Lean_SourceInfo_fromRef(v_ref_3551_, v___x_3401_);
v___x_3555_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3554_, 7);
v___x_3558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3554_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3560_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3561_ = lean_box(0);
lean_inc(v_currMacroScope_3553_);
lean_inc(v_quotContext_3552_);
v___x_3562_ = l_Lean_addMacroScope(v_quotContext_3552_, v___x_3561_, v_currMacroScope_3553_);
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3564_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3554_);
lean_ctor_set(v___x_3564_, 1, v___x_3560_);
lean_ctor_set(v___x_3564_, 2, v___x_3562_);
lean_ctor_set(v___x_3564_, 3, v___x_3563_);
v___x_3565_ = l_Lean_Syntax_node1(v___x_3554_, v___x_3559_, v___x_3564_);
v___x_3566_ = l_Lean_Syntax_node2(v___x_3554_, v___x_3556_, v___x_3558_, v___x_3565_);
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3554_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3570_ = l_Lean_Syntax_node1(v___x_3554_, v___x_3569_, v_val_3550_);
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3554_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_Syntax_node5(v___x_3554_, v___x_3555_, v___x_3566_, v___x_3549_, v___x_3568_, v___x_3570_, v___x_3572_);
v_rhs_3521_ = v___x_3573_;
v___y_3522_ = v___y_3541_;
v___y_3523_ = v___y_3542_;
v___y_3524_ = v___y_3543_;
v___y_3525_ = v___y_3544_;
v___y_3526_ = v___y_3545_;
v___y_3527_ = v___y_3546_;
v___y_3528_ = v___y_3547_;
goto v___jp_3520_;
}
}
}
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_del_object(v___x_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3380_);
v___x_3588_ = lean_box(v___x_3396_);
lean_inc(v___x_3399_);
v___x_3589_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3589_, 0, v___x_3399_);
lean_closure_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3589_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v_ref_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v_ref_3592_ = lean_ctor_get(v_a_3375_, 5);
v___x_3593_ = 0;
v___x_3594_ = l_Lean_SourceInfo_fromRef(v_ref_3592_, v___x_3593_);
v___x_3595_ = l_Lean_Syntax_node1(v___x_3594_, v___x_3395_, v_a_3591_);
lean_inc(v___x_3595_);
v___x_3596_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3596_, 0, v_config_3365_);
lean_closure_set(v___x_3596_, 1, v_letOrReassign_3366_);
lean_closure_set(v___x_3596_, 2, v___x_3595_);
lean_closure_set(v___x_3596_, 3, v_tk_3368_);
lean_closure_set(v___x_3596_, 4, v_a_3383_);
v___x_3597_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3399_, v___x_3595_, v___x_3596_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
return v___x_3597_;
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec(v___x_3399_);
lean_dec(v_a_3383_);
lean_dec(v_tk_3368_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3598_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3590_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3590_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3385_);
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_tk_3368_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
return v___x_3387_;
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v_a_3383_);
lean_dec(v_a_3380_);
lean_dec(v_tk_3368_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3607_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3384_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3384_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_a_3380_);
lean_dec(v_tk_3368_);
lean_dec(v_decl_3367_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3615_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3382_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3382_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_a_3380_);
lean_dec_ref(v_dec_3369_);
lean_dec(v_tk_3368_);
lean_dec(v_decl_3367_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3623_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3381_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3381_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v_dec_3369_);
lean_dec(v_tk_3368_);
lean_dec(v_decl_3367_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3631_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3379_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3379_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_dec_3369_);
lean_dec(v_tk_3368_);
lean_dec(v_decl_3367_);
lean_dec(v_letOrReassign_3366_);
lean_dec_ref(v_config_3365_);
v_a_3639_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3378_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3378_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3648_, v_x_3649_, v_x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3652_, lean_object* v_msg_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3652_, v_msg_3653_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3663_, lean_object* v_msg_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3663_, v_msg_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3679_, v___y_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3692_, lean_object* v_beforeStx_3693_, lean_object* v_afterStx_3694_, lean_object* v_x_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3693_, v_afterStx_3694_, v_x_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3705_, lean_object* v_beforeStx_3706_, lean_object* v_afterStx_3707_, lean_object* v_x_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3705_, v_beforeStx_3706_, v_afterStx_3707_, v_x_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3718_, lean_object* v_x_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3719_, v___y_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3723_, lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3723_, v_x_3724_, v___y_3725_, v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_x_3724_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3728_, lean_object* v_ref_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3729_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_ref_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3739_, v_ref_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3750_, lean_object* v_x_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3761_, lean_object* v_x_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3761_, v_x_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v___y_3763_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3772_, lean_object* v_x_3773_, size_t v_x_3774_, size_t v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3773_, v_x_3774_, v_x_3775_, v_x_3776_, v_x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3779_, lean_object* v_x_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_){
_start:
{
size_t v_x_102821__boxed_3785_; size_t v_x_102822__boxed_3786_; lean_object* v_res_3787_; 
v_x_102821__boxed_3785_ = lean_unbox_usize(v_x_3781_);
lean_dec(v_x_3781_);
v_x_102822__boxed_3786_ = lean_unbox_usize(v_x_3782_);
lean_dec(v_x_3782_);
v_res_3787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3779_, v_x_3780_, v_x_102821__boxed_3785_, v_x_102822__boxed_3786_, v_x_3783_, v_x_3784_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3788_, lean_object* v_stx_3789_, lean_object* v_output_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3789_, v_output_3790_, v_x_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3800_, lean_object* v_stx_3801_, lean_object* v_output_3802_, lean_object* v_x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3800_, v_stx_3801_, v_output_3802_, v_x_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3812_, lean_object* v_as_x27_3813_, lean_object* v_b_3814_, lean_object* v_a_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3813_, v_b_3814_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3825_, lean_object* v_as_x27_3826_, lean_object* v_b_3827_, lean_object* v_a_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3825_, v_as_x27_3826_, v_b_3827_, v_a_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v_as_x27_3826_);
lean_dec(v_as_3825_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3838_, lean_object* v_ref_3839_, lean_object* v_msg_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3839_, v_msg_3840_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_ref_3851_, lean_object* v_msg_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3850_, v_ref_3851_, v_msg_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v_ref_3851_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3862_, lean_object* v_n_3863_, lean_object* v_k_3864_, lean_object* v_v_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3863_, v_k_3864_, v_v_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3867_, size_t v_depth_3868_, lean_object* v_keys_3869_, lean_object* v_vals_3870_, lean_object* v_heq_3871_, lean_object* v_i_3872_, lean_object* v_entries_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3868_, v_keys_3869_, v_vals_3870_, v_i_3872_, v_entries_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3875_, lean_object* v_depth_3876_, lean_object* v_keys_3877_, lean_object* v_vals_3878_, lean_object* v_heq_3879_, lean_object* v_i_3880_, lean_object* v_entries_3881_){
_start:
{
size_t v_depth_boxed_3882_; lean_object* v_res_3883_; 
v_depth_boxed_3882_ = lean_unbox_usize(v_depth_3876_);
lean_dec(v_depth_3876_);
v_res_3883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3875_, v_depth_boxed_3882_, v_keys_3877_, v_vals_3878_, v_heq_3879_, v_i_3880_, v_entries_3881_);
lean_dec_ref(v_vals_3878_);
lean_dec_ref(v_keys_3877_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3900_, lean_object* v_x_3901_, lean_object* v_mkInfoTree_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3901_, v_mkInfoTree_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3911_, lean_object* v_x_3912_, lean_object* v_mkInfoTree_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3911_, v_x_3912_, v_mkInfoTree_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3923_, v_x_3924_, v_x_3925_, v_x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_){
_start:
{
uint8_t v_res_3935_; lean_object* v_r_3936_; 
v_res_3935_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3932_, v_x_3933_, v_x_3934_);
lean_dec_ref(v_x_3934_);
lean_dec_ref(v_x_3933_);
v_r_3936_ = lean_box(v_res_3935_);
return v_r_3936_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3937_, lean_object* v_x_3938_, size_t v_x_3939_, lean_object* v_x_3940_){
_start:
{
uint8_t v___x_3941_; 
v___x_3941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3938_, v_x_3939_, v_x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3942_, lean_object* v_x_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_){
_start:
{
size_t v_x_102984__boxed_3946_; uint8_t v_res_3947_; lean_object* v_r_3948_; 
v_x_102984__boxed_3946_ = lean_unbox_usize(v_x_3944_);
lean_dec(v_x_3944_);
v_res_3947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3942_, v_x_3943_, v_x_102984__boxed_3946_, v_x_3945_);
lean_dec_ref(v_x_3945_);
lean_dec_ref(v_x_3943_);
v_r_3948_ = lean_box(v_res_3947_);
return v_r_3948_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27(lean_object* v_00_u03b2_3949_, lean_object* v_keys_3950_, lean_object* v_vals_3951_, lean_object* v_heq_3952_, lean_object* v_i_3953_, lean_object* v_k_3954_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___redArg(v_keys_3950_, v_i_3953_, v_k_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27___boxed(lean_object* v_00_u03b2_3956_, lean_object* v_keys_3957_, lean_object* v_vals_3958_, lean_object* v_heq_3959_, lean_object* v_i_3960_, lean_object* v_k_3961_){
_start:
{
uint8_t v_res_3962_; lean_object* v_r_3963_; 
v_res_3962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__27(v_00_u03b2_3956_, v_keys_3957_, v_vals_3958_, v_heq_3959_, v_i_3960_, v_k_3961_);
lean_dec_ref(v_k_3961_);
lean_dec_ref(v_vals_3958_);
lean_dec_ref(v_keys_3957_);
v_r_3963_ = lean_box(v_res_3962_);
return v_r_3963_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3973_, lean_object* v_otherwise_x3f_3974_, uint8_t v___x_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v___x_3980_, lean_object* v_dec_3981_, uint8_t v___x_3982_, lean_object* v___y_3983_, lean_object* v___x_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; uint8_t v___y_4016_; 
switch(lean_obj_tag(v_letOrReassign_3973_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3974_) == 1)
{
lean_object* v_mutTk_x3f_4027_; lean_object* v_val_4028_; lean_object* v_ref_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4059_; 
v_mutTk_x3f_4027_ = lean_ctor_get(v_letOrReassign_3973_, 0);
v_val_4028_ = lean_ctor_get(v_otherwise_x3f_3974_, 0);
lean_inc(v_val_4028_);
lean_dec_ref(v_otherwise_x3f_3974_);
v_ref_4029_ = lean_ctor_get(v___y_3990_, 5);
v___x_4030_ = l_Lean_SourceInfo_fromRef(v_ref_4029_, v___x_3975_);
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
lean_inc_ref(v___x_3976_);
v___x_4032_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4031_);
v___x_4033_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4030_);
v___x_4034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4030_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4036_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4027_) == 1)
{
lean_object* v_val_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v_val_4074_ = lean_ctor_get(v_mutTk_x3f_4027_, 0);
v___x_4075_ = l_Lean_SourceInfo_fromRef(v_val_4074_, v___x_3982_);
v___x_4076_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4075_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_Array_mkArray1___redArg(v___x_4077_);
v___y_4059_ = v___x_4078_;
goto v___jp_4058_;
}
else
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_mk_empty_array_with_capacity(v___x_3984_);
v___y_4059_ = v___x_4079_;
goto v___jp_4058_;
}
v___jp_4037_:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4043_ = l_Array_append___redArg(v___x_4036_, v___y_4042_);
lean_dec_ref(v___y_4042_);
lean_inc(v___x_4030_);
v___x_4044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4030_);
lean_ctor_set(v___x_4044_, 1, v___x_4035_);
lean_ctor_set(v___x_4044_, 2, v___x_4043_);
v___x_4045_ = lean_unsigned_to_nat(9u);
v___x_4046_ = lean_mk_empty_array_with_capacity(v___x_4045_);
v___x_4047_ = lean_array_push(v___x_4046_, v___x_4034_);
v___x_4048_ = lean_array_push(v___x_4047_, v___y_4039_);
v___x_4049_ = lean_array_push(v___x_4048_, v___y_4041_);
v___x_4050_ = lean_array_push(v___x_4049_, v___x_3979_);
v___x_4051_ = lean_array_push(v___x_4050_, v___y_4038_);
v___x_4052_ = lean_array_push(v___x_4051_, v___x_3980_);
v___x_4053_ = lean_array_push(v___x_4052_, v___y_4040_);
v___x_4054_ = lean_array_push(v___x_4053_, v_val_4028_);
v___x_4055_ = lean_array_push(v___x_4054_, v___x_4044_);
v___x_4056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4030_);
lean_ctor_set(v___x_4056_, 1, v___x_4032_);
lean_ctor_set(v___x_4056_, 2, v___x_4055_);
v___x_4057_ = l_Lean_Elab_Do_elabDoElem(v___x_4056_, v_dec_3981_, v___x_3982_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_4057_;
}
v___jp_4058_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4060_ = l_Array_append___redArg(v___x_4036_, v___y_4059_);
lean_dec_ref(v___y_4059_);
lean_inc_n(v___x_4030_, 5);
v___x_4061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4030_);
lean_ctor_set(v___x_4061_, 1, v___x_4035_);
lean_ctor_set(v___x_4061_, 2, v___x_4060_);
v___x_4062_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4063_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4030_);
lean_ctor_set(v___x_4064_, 1, v___x_4035_);
lean_ctor_set(v___x_4064_, 2, v___x_4036_);
v___x_4065_ = l_Lean_Syntax_node1(v___x_4030_, v___x_4063_, v___x_4064_);
v___x_4066_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4030_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4030_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
if (lean_obj_tag(v___y_3983_) == 0)
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_mk_empty_array_with_capacity(v___x_3984_);
v___y_4038_ = v___x_4067_;
v___y_4039_ = v___x_4061_;
v___y_4040_ = v___x_4069_;
v___y_4041_ = v___x_4065_;
v___y_4042_ = v___x_4070_;
goto v___jp_4037_;
}
else
{
lean_object* v_val_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_val_4071_ = lean_ctor_get(v___y_3983_, 0);
lean_inc(v_val_4071_);
lean_dec_ref(v___y_3983_);
v___x_4072_ = lean_mk_empty_array_with_capacity(v___x_3984_);
v___x_4073_ = lean_array_push(v___x_4072_, v_val_4071_);
v___y_4038_ = v___x_4067_;
v___y_4039_ = v___x_4061_;
v___y_4040_ = v___x_4069_;
v___y_4041_ = v___x_4065_;
v___y_4042_ = v___x_4073_;
goto v___jp_4037_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4080_; lean_object* v_ref_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___y_4090_; 
lean_dec(v___y_3983_);
lean_dec(v_otherwise_x3f_3974_);
v_mutTk_x3f_4080_ = lean_ctor_get(v_letOrReassign_3973_, 0);
v_ref_4081_ = lean_ctor_get(v___y_3990_, 5);
v___x_4082_ = l_Lean_SourceInfo_fromRef(v_ref_4081_, v___x_3975_);
v___x_4083_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
lean_inc_ref(v___x_3976_);
v___x_4084_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4083_);
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4082_);
v___x_4086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4082_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4088_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4080_) == 1)
{
lean_object* v_val_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_val_4107_ = lean_ctor_get(v_mutTk_x3f_4080_, 0);
v___x_4108_ = l_Lean_SourceInfo_fromRef(v_val_4107_, v___x_3982_);
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Array_mkArray1___redArg(v___x_4110_);
v___y_4090_ = v___x_4111_;
goto v___jp_4089_;
}
else
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_mk_empty_array_with_capacity(v___x_3984_);
v___y_4090_ = v___x_4112_;
goto v___jp_4089_;
}
v___jp_4089_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4091_ = l_Array_append___redArg(v___x_4088_, v___y_4090_);
lean_dec_ref(v___y_4090_);
lean_inc_n(v___x_4082_, 6);
v___x_4092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4082_);
lean_ctor_set(v___x_4092_, 1, v___x_4087_);
lean_ctor_set(v___x_4092_, 2, v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3978_, 2);
lean_inc_ref_n(v___x_3977_, 2);
lean_inc_ref_n(v___x_3976_, 2);
v___x_4094_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4082_);
lean_ctor_set(v___x_4095_, 1, v___x_4087_);
lean_ctor_set(v___x_4095_, 2, v___x_4088_);
lean_inc_ref_n(v___x_4095_, 2);
v___x_4096_ = l_Lean_Syntax_node1(v___x_4082_, v___x_4094_, v___x_4095_);
v___x_4097_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4098_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4097_);
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4100_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4099_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4082_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = l_Lean_Syntax_node5(v___x_4082_, v___x_4100_, v___x_3979_, v___x_4095_, v___x_4095_, v___x_4102_, v___x_3980_);
v___x_4104_ = l_Lean_Syntax_node1(v___x_4082_, v___x_4098_, v___x_4103_);
v___x_4105_ = l_Lean_Syntax_node4(v___x_4082_, v___x_4084_, v___x_4086_, v___x_4092_, v___x_4096_, v___x_4104_);
v___x_4106_ = l_Lean_Elab_Do_elabDoElem(v___x_4105_, v_dec_3981_, v___x_3982_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_4106_;
}
}
}
case 1:
{
lean_dec(v___y_3983_);
if (lean_obj_tag(v_otherwise_x3f_3974_) == 1)
{
lean_object* v___x_4113_; 
lean_dec_ref(v_otherwise_x3f_3974_);
lean_dec_ref(v_dec_3981_);
lean_dec(v___x_3980_);
lean_dec(v___x_3979_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v___x_3977_);
lean_dec_ref(v___x_3976_);
v___x_4113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4113_;
}
else
{
lean_object* v_ref_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec(v_otherwise_x3f_3974_);
v_ref_4114_ = lean_ctor_get(v___y_3990_, 5);
v___x_4115_ = l_Lean_SourceInfo_fromRef(v_ref_4114_, v___x_3975_);
v___x_4116_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3978_, 3);
lean_inc_ref_n(v___x_3977_, 3);
lean_inc_ref_n(v___x_3976_, 3);
v___x_4117_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4116_);
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4115_, 6);
v___x_4119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4115_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4121_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4120_);
v___x_4122_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4123_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4115_);
lean_ctor_set(v___x_4124_, 1, v___x_4122_);
lean_ctor_set(v___x_4124_, 2, v___x_4123_);
lean_inc_ref_n(v___x_4124_, 2);
v___x_4125_ = l_Lean_Syntax_node1(v___x_4115_, v___x_4121_, v___x_4124_);
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4127_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4126_);
v___x_4128_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4129_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4128_);
v___x_4130_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4115_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_Syntax_node5(v___x_4115_, v___x_4129_, v___x_3979_, v___x_4124_, v___x_4124_, v___x_4131_, v___x_3980_);
v___x_4133_ = l_Lean_Syntax_node1(v___x_4115_, v___x_4127_, v___x_4132_);
v___x_4134_ = l_Lean_Syntax_node3(v___x_4115_, v___x_4117_, v___x_4119_, v___x_4125_, v___x_4133_);
v___x_4135_ = l_Lean_Elab_Do_elabDoElem(v___x_4134_, v_dec_3981_, v___x_3982_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_4135_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3974_);
if (lean_obj_tag(v___y_3983_) == 0)
{
v___y_4016_ = v___x_3982_;
goto v___jp_4015_;
}
else
{
lean_dec_ref(v___y_3983_);
v___y_4016_ = v___x_3975_;
goto v___jp_4015_;
}
}
}
v___jp_3993_:
{
lean_object* v_ref_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_ref_4001_ = lean_ctor_get(v___y_3999_, 5);
v___x_4002_ = l_Lean_SourceInfo_fromRef(v_ref_4001_, v___x_3975_);
v___x_4003_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
lean_inc_ref(v___x_3976_);
v___x_4004_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4003_);
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4006_ = l_Lean_Name_mkStr4(v___x_3976_, v___x_3977_, v___x_3978_, v___x_4005_);
v___x_4007_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4008_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4002_, 3);
v___x_4009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4002_);
lean_ctor_set(v___x_4009_, 1, v___x_4007_);
lean_ctor_set(v___x_4009_, 2, v___x_4008_);
v___x_4010_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4002_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
lean_inc_ref(v___x_4009_);
v___x_4012_ = l_Lean_Syntax_node5(v___x_4002_, v___x_4006_, v___x_3979_, v___x_4009_, v___x_4009_, v___x_4011_, v___x_3980_);
v___x_4013_ = l_Lean_Syntax_node1(v___x_4002_, v___x_4004_, v___x_4012_);
v___x_4014_ = l_Lean_Elab_Do_elabDoElem(v___x_4013_, v_dec_3981_, v___x_3982_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
return v___x_4014_;
}
v___jp_4015_:
{
if (v___y_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec_ref(v_dec_3981_);
lean_dec(v___x_3980_);
lean_dec(v___x_3979_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v___x_3977_);
lean_dec_ref(v___x_3976_);
v___x_4017_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4018_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4017_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
v___y_3994_ = v___y_3985_;
v___y_3995_ = v___y_3986_;
v___y_3996_ = v___y_3987_;
v___y_3997_ = v___y_3988_;
v___y_3998_ = v___y_3989_;
v___y_3999_ = v___y_3990_;
v___y_4000_ = v___y_3991_;
goto v___jp_3993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4136_ = _args[0];
lean_object* v_otherwise_x3f_4137_ = _args[1];
lean_object* v___x_4138_ = _args[2];
lean_object* v___x_4139_ = _args[3];
lean_object* v___x_4140_ = _args[4];
lean_object* v___x_4141_ = _args[5];
lean_object* v___x_4142_ = _args[6];
lean_object* v___x_4143_ = _args[7];
lean_object* v_dec_4144_ = _args[8];
lean_object* v___x_4145_ = _args[9];
lean_object* v___y_4146_ = _args[10];
lean_object* v___x_4147_ = _args[11];
lean_object* v___y_4148_ = _args[12];
lean_object* v___y_4149_ = _args[13];
lean_object* v___y_4150_ = _args[14];
lean_object* v___y_4151_ = _args[15];
lean_object* v___y_4152_ = _args[16];
lean_object* v___y_4153_ = _args[17];
lean_object* v___y_4154_ = _args[18];
lean_object* v___y_4155_ = _args[19];
_start:
{
uint8_t v___x_39025__boxed_4156_; uint8_t v___x_39031__boxed_4157_; lean_object* v_res_4158_; 
v___x_39025__boxed_4156_ = lean_unbox(v___x_4138_);
v___x_39031__boxed_4157_ = lean_unbox(v___x_4145_);
v_res_4158_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4136_, v_otherwise_x3f_4137_, v___x_39025__boxed_4156_, v___x_4139_, v___x_4140_, v___x_4141_, v___x_4142_, v___x_4143_, v_dec_4144_, v___x_39031__boxed_4157_, v___y_4146_, v___x_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___x_4147_);
lean_dec(v_letOrReassign_4136_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4159_, lean_object* v_otherwise_x3f_4160_, uint8_t v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v_dec_4167_, uint8_t v___x_4168_, lean_object* v___y_4169_, lean_object* v___x_4170_, uint8_t v___x_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; uint8_t v___y_4203_; 
switch(lean_obj_tag(v_letOrReassign_4159_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4160_) == 1)
{
lean_object* v_mutTk_x3f_4214_; lean_object* v_val_4215_; lean_object* v_ref_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4246_; 
v_mutTk_x3f_4214_ = lean_ctor_get(v_letOrReassign_4159_, 0);
v_val_4215_ = lean_ctor_get(v_otherwise_x3f_4160_, 0);
lean_inc(v_val_4215_);
lean_dec_ref(v_otherwise_x3f_4160_);
v_ref_4216_ = lean_ctor_get(v___y_4177_, 5);
v___x_4217_ = l_Lean_SourceInfo_fromRef(v_ref_4216_, v___x_4161_);
v___x_4218_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
lean_inc_ref(v___x_4162_);
v___x_4219_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4218_);
v___x_4220_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4217_);
v___x_4221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4217_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
v___x_4222_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4223_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4214_) == 1)
{
lean_object* v_val_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_val_4261_ = lean_ctor_get(v_mutTk_x3f_4214_, 0);
v___x_4262_ = l_Lean_SourceInfo_fromRef(v_val_4261_, v___x_4168_);
v___x_4263_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = l_Array_mkArray1___redArg(v___x_4264_);
v___y_4246_ = v___x_4265_;
goto v___jp_4245_;
}
else
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_mk_empty_array_with_capacity(v___x_4170_);
v___y_4246_ = v___x_4266_;
goto v___jp_4245_;
}
v___jp_4224_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4230_ = l_Array_append___redArg(v___x_4223_, v___y_4229_);
lean_dec_ref(v___y_4229_);
lean_inc(v___x_4217_);
v___x_4231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4217_);
lean_ctor_set(v___x_4231_, 1, v___x_4222_);
lean_ctor_set(v___x_4231_, 2, v___x_4230_);
v___x_4232_ = lean_unsigned_to_nat(9u);
v___x_4233_ = lean_mk_empty_array_with_capacity(v___x_4232_);
v___x_4234_ = lean_array_push(v___x_4233_, v___x_4221_);
v___x_4235_ = lean_array_push(v___x_4234_, v___y_4227_);
v___x_4236_ = lean_array_push(v___x_4235_, v___y_4226_);
v___x_4237_ = lean_array_push(v___x_4236_, v___x_4165_);
v___x_4238_ = lean_array_push(v___x_4237_, v___y_4225_);
v___x_4239_ = lean_array_push(v___x_4238_, v___x_4166_);
v___x_4240_ = lean_array_push(v___x_4239_, v___y_4228_);
v___x_4241_ = lean_array_push(v___x_4240_, v_val_4215_);
v___x_4242_ = lean_array_push(v___x_4241_, v___x_4231_);
v___x_4243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4217_);
lean_ctor_set(v___x_4243_, 1, v___x_4219_);
lean_ctor_set(v___x_4243_, 2, v___x_4242_);
v___x_4244_ = l_Lean_Elab_Do_elabDoElem(v___x_4243_, v_dec_4167_, v___x_4168_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4244_;
}
v___jp_4245_:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4247_ = l_Array_append___redArg(v___x_4223_, v___y_4246_);
lean_dec_ref(v___y_4246_);
lean_inc_n(v___x_4217_, 5);
v___x_4248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4217_);
lean_ctor_set(v___x_4248_, 1, v___x_4222_);
lean_ctor_set(v___x_4248_, 2, v___x_4247_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4250_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4249_);
v___x_4251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4217_);
lean_ctor_set(v___x_4251_, 1, v___x_4222_);
lean_ctor_set(v___x_4251_, 2, v___x_4223_);
v___x_4252_ = l_Lean_Syntax_node1(v___x_4217_, v___x_4250_, v___x_4251_);
v___x_4253_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4217_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4217_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
if (lean_obj_tag(v___y_4169_) == 0)
{
lean_object* v___x_4257_; 
v___x_4257_ = lean_mk_empty_array_with_capacity(v___x_4170_);
v___y_4225_ = v___x_4254_;
v___y_4226_ = v___x_4252_;
v___y_4227_ = v___x_4248_;
v___y_4228_ = v___x_4256_;
v___y_4229_ = v___x_4257_;
goto v___jp_4224_;
}
else
{
lean_object* v_val_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_val_4258_ = lean_ctor_get(v___y_4169_, 0);
lean_inc(v_val_4258_);
lean_dec_ref(v___y_4169_);
v___x_4259_ = lean_mk_empty_array_with_capacity(v___x_4170_);
v___x_4260_ = lean_array_push(v___x_4259_, v_val_4258_);
v___y_4225_ = v___x_4254_;
v___y_4226_ = v___x_4252_;
v___y_4227_ = v___x_4248_;
v___y_4228_ = v___x_4256_;
v___y_4229_ = v___x_4260_;
goto v___jp_4224_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4267_; lean_object* v_ref_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___y_4277_; 
lean_dec(v___y_4169_);
lean_dec(v_otherwise_x3f_4160_);
v_mutTk_x3f_4267_ = lean_ctor_get(v_letOrReassign_4159_, 0);
v_ref_4268_ = lean_ctor_get(v___y_4177_, 5);
v___x_4269_ = l_Lean_SourceInfo_fromRef(v_ref_4268_, v___x_4161_);
v___x_4270_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
lean_inc_ref(v___x_4162_);
v___x_4271_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4270_);
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4269_);
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4269_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4275_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4267_) == 1)
{
lean_object* v_val_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_val_4294_ = lean_ctor_get(v_mutTk_x3f_4267_, 0);
v___x_4295_ = l_Lean_SourceInfo_fromRef(v_val_4294_, v___x_4168_);
v___x_4296_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = l_Array_mkArray1___redArg(v___x_4297_);
v___y_4277_ = v___x_4298_;
goto v___jp_4276_;
}
else
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_mk_empty_array_with_capacity(v___x_4170_);
v___y_4277_ = v___x_4299_;
goto v___jp_4276_;
}
v___jp_4276_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4278_ = l_Array_append___redArg(v___x_4275_, v___y_4277_);
lean_dec_ref(v___y_4277_);
lean_inc_n(v___x_4269_, 6);
v___x_4279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4269_);
lean_ctor_set(v___x_4279_, 1, v___x_4274_);
lean_ctor_set(v___x_4279_, 2, v___x_4278_);
v___x_4280_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4164_, 2);
lean_inc_ref_n(v___x_4163_, 2);
lean_inc_ref_n(v___x_4162_, 2);
v___x_4281_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4269_);
lean_ctor_set(v___x_4282_, 1, v___x_4274_);
lean_ctor_set(v___x_4282_, 2, v___x_4275_);
lean_inc_ref_n(v___x_4282_, 2);
v___x_4283_ = l_Lean_Syntax_node1(v___x_4269_, v___x_4281_, v___x_4282_);
v___x_4284_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4285_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4284_);
v___x_4286_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4287_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4286_);
v___x_4288_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4269_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = l_Lean_Syntax_node5(v___x_4269_, v___x_4287_, v___x_4165_, v___x_4282_, v___x_4282_, v___x_4289_, v___x_4166_);
v___x_4291_ = l_Lean_Syntax_node1(v___x_4269_, v___x_4285_, v___x_4290_);
v___x_4292_ = l_Lean_Syntax_node4(v___x_4269_, v___x_4271_, v___x_4273_, v___x_4279_, v___x_4283_, v___x_4291_);
v___x_4293_ = l_Lean_Elab_Do_elabDoElem(v___x_4292_, v_dec_4167_, v___x_4168_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4293_;
}
}
}
case 1:
{
lean_dec(v___y_4169_);
if (lean_obj_tag(v_otherwise_x3f_4160_) == 1)
{
lean_object* v___x_4300_; 
lean_dec_ref(v_otherwise_x3f_4160_);
lean_dec_ref(v_dec_4167_);
lean_dec(v___x_4166_);
lean_dec(v___x_4165_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v___x_4163_);
lean_dec_ref(v___x_4162_);
v___x_4300_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4300_;
}
else
{
lean_object* v_ref_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
lean_dec(v_otherwise_x3f_4160_);
v_ref_4301_ = lean_ctor_get(v___y_4177_, 5);
v___x_4302_ = l_Lean_SourceInfo_fromRef(v_ref_4301_, v___x_4161_);
v___x_4303_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4164_, 3);
lean_inc_ref_n(v___x_4163_, 3);
lean_inc_ref_n(v___x_4162_, 3);
v___x_4304_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4303_);
v___x_4305_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4302_, 6);
v___x_4306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4302_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4308_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4307_);
v___x_4309_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4310_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4302_);
lean_ctor_set(v___x_4311_, 1, v___x_4309_);
lean_ctor_set(v___x_4311_, 2, v___x_4310_);
lean_inc_ref_n(v___x_4311_, 2);
v___x_4312_ = l_Lean_Syntax_node1(v___x_4302_, v___x_4308_, v___x_4311_);
v___x_4313_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4314_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4313_);
v___x_4315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4316_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4315_);
v___x_4317_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4302_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l_Lean_Syntax_node5(v___x_4302_, v___x_4316_, v___x_4165_, v___x_4311_, v___x_4311_, v___x_4318_, v___x_4166_);
v___x_4320_ = l_Lean_Syntax_node1(v___x_4302_, v___x_4314_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_node3(v___x_4302_, v___x_4304_, v___x_4306_, v___x_4312_, v___x_4320_);
v___x_4322_ = l_Lean_Elab_Do_elabDoElem(v___x_4321_, v_dec_4167_, v___x_4168_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4322_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4160_);
if (lean_obj_tag(v___y_4169_) == 0)
{
v___y_4203_ = v___x_4171_;
goto v___jp_4202_;
}
else
{
lean_dec_ref(v___y_4169_);
v___y_4203_ = v___x_4161_;
goto v___jp_4202_;
}
}
}
v___jp_4180_:
{
lean_object* v_ref_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_ref_4188_ = lean_ctor_get(v___y_4186_, 5);
v___x_4189_ = l_Lean_SourceInfo_fromRef(v_ref_4188_, v___x_4161_);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
lean_inc_ref(v___x_4162_);
v___x_4191_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4190_);
v___x_4192_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4193_ = l_Lean_Name_mkStr4(v___x_4162_, v___x_4163_, v___x_4164_, v___x_4192_);
v___x_4194_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4195_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4189_, 3);
v___x_4196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4189_);
lean_ctor_set(v___x_4196_, 1, v___x_4194_);
lean_ctor_set(v___x_4196_, 2, v___x_4195_);
v___x_4197_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4189_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
lean_inc_ref(v___x_4196_);
v___x_4199_ = l_Lean_Syntax_node5(v___x_4189_, v___x_4193_, v___x_4165_, v___x_4196_, v___x_4196_, v___x_4198_, v___x_4166_);
v___x_4200_ = l_Lean_Syntax_node1(v___x_4189_, v___x_4191_, v___x_4199_);
v___x_4201_ = l_Lean_Elab_Do_elabDoElem(v___x_4200_, v_dec_4167_, v___x_4168_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4201_;
}
v___jp_4202_:
{
if (v___y_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v_dec_4167_);
lean_dec(v___x_4166_);
lean_dec(v___x_4165_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v___x_4163_);
lean_dec_ref(v___x_4162_);
v___x_4204_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4205_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4204_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4205_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
else
{
v___y_4181_ = v___y_4172_;
v___y_4182_ = v___y_4173_;
v___y_4183_ = v___y_4174_;
v___y_4184_ = v___y_4175_;
v___y_4185_ = v___y_4176_;
v___y_4186_ = v___y_4177_;
v___y_4187_ = v___y_4178_;
goto v___jp_4180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4323_ = _args[0];
lean_object* v_otherwise_x3f_4324_ = _args[1];
lean_object* v___x_4325_ = _args[2];
lean_object* v___x_4326_ = _args[3];
lean_object* v___x_4327_ = _args[4];
lean_object* v___x_4328_ = _args[5];
lean_object* v___x_4329_ = _args[6];
lean_object* v___x_4330_ = _args[7];
lean_object* v_dec_4331_ = _args[8];
lean_object* v___x_4332_ = _args[9];
lean_object* v___y_4333_ = _args[10];
lean_object* v___x_4334_ = _args[11];
lean_object* v___x_4335_ = _args[12];
lean_object* v___y_4336_ = _args[13];
lean_object* v___y_4337_ = _args[14];
lean_object* v___y_4338_ = _args[15];
lean_object* v___y_4339_ = _args[16];
lean_object* v___y_4340_ = _args[17];
lean_object* v___y_4341_ = _args[18];
lean_object* v___y_4342_ = _args[19];
lean_object* v___y_4343_ = _args[20];
_start:
{
uint8_t v___x_39407__boxed_4344_; uint8_t v___x_39413__boxed_4345_; uint8_t v___x_39416__boxed_4346_; lean_object* v_res_4347_; 
v___x_39407__boxed_4344_ = lean_unbox(v___x_4325_);
v___x_39413__boxed_4345_ = lean_unbox(v___x_4332_);
v___x_39416__boxed_4346_ = lean_unbox(v___x_4335_);
v_res_4347_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4323_, v_otherwise_x3f_4324_, v___x_39407__boxed_4344_, v___x_4326_, v___x_4327_, v___x_4328_, v___x_4329_, v___x_4330_, v_dec_4331_, v___x_39413__boxed_4345_, v___y_4333_, v___x_4334_, v___x_39416__boxed_4346_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___x_4334_);
lean_dec(v_letOrReassign_4323_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4368_, lean_object* v_stx_4369_, lean_object* v_tk_4370_, lean_object* v_dec_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4380_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4382_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4383_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4369_);
v___x_4384_ = l_Lean_Syntax_isOfKind(v_stx_4369_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4369_);
v___x_4386_ = l_Lean_Syntax_isOfKind(v_stx_4369_, v___x_4385_);
if (v___x_4386_ == 0)
{
lean_object* v___x_4387_; 
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4387_;
}
else
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; 
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4388_);
v___x_4390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4389_);
v___x_4391_ = l_Lean_Syntax_isOfKind(v___x_4389_, v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4477_; lean_object* v_patType_x3f_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4477_ = lean_unsigned_to_nat(1u);
v___x_4508_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4477_);
v___x_4509_ = l_Lean_Syntax_isNone(v___x_4508_);
if (v___x_4509_ == 0)
{
uint8_t v___x_4510_; 
lean_inc(v___x_4508_);
v___x_4510_ = l_Lean_Syntax_matchesNull(v___x_4508_, v___x_4477_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_dec(v___x_4508_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = l_Lean_Syntax_getArg(v___x_4508_, v___x_4388_);
lean_dec(v___x_4508_);
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4512_);
v___x_4514_ = l_Lean_Syntax_isOfKind(v___x_4512_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; 
lean_dec(v___x_4512_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4515_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4515_;
}
else
{
lean_object* v_patType_x3f_4516_; lean_object* v___x_4517_; 
v_patType_x3f_4516_ = l_Lean_Syntax_getArg(v___x_4512_, v___x_4477_);
lean_dec(v___x_4512_);
v___x_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4517_, 0, v_patType_x3f_4516_);
v_patType_x3f_4479_ = v___x_4517_;
v___y_4480_ = v_a_4372_;
v___y_4481_ = v_a_4373_;
v___y_4482_ = v_a_4374_;
v___y_4483_ = v_a_4375_;
v___y_4484_ = v_a_4376_;
v___y_4485_ = v_a_4377_;
v___y_4486_ = v_a_4378_;
goto v___jp_4478_;
}
}
}
else
{
lean_object* v___x_4518_; 
lean_dec(v___x_4508_);
v___x_4518_ = lean_box(0);
v_patType_x3f_4479_ = v___x_4518_;
v___y_4480_ = v_a_4372_;
v___y_4481_ = v_a_4373_;
v___y_4482_ = v_a_4374_;
v___y_4483_ = v_a_4375_;
v___y_4484_ = v_a_4376_;
v___y_4485_ = v_a_4377_;
v___y_4486_ = v_a_4378_;
goto v___jp_4478_;
}
v___jp_4478_:
{
lean_object* v___x_4487_; lean_object* v_rhs_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4487_ = lean_unsigned_to_nat(3u);
v_rhs_4488_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4487_);
v___x_4489_ = lean_unsigned_to_nat(4u);
v___x_4490_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4489_);
lean_dec(v_stx_4369_);
v___x_4491_ = l_Lean_Syntax_isNone(v___x_4490_);
if (v___x_4491_ == 0)
{
uint8_t v___x_4492_; 
lean_inc(v___x_4490_);
v___x_4492_ = l_Lean_Syntax_matchesNull(v___x_4490_, v___x_4487_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_dec(v___x_4490_);
lean_dec(v_rhs_4488_);
lean_dec(v_patType_x3f_4479_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_letOrReassign_4368_);
v___x_4493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v_otherwise_x3f_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4494_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4495_ = l_Lean_Syntax_getArg(v___x_4490_, v___x_4477_);
v___x_4496_ = l_Lean_Syntax_getArg(v___x_4490_, v___x_4494_);
lean_dec(v___x_4490_);
v___x_4497_ = l_Lean_Syntax_getOptional_x3f(v___x_4496_);
lean_dec(v___x_4496_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_box(0);
v___y_4422_ = v___y_4484_;
v___y_4423_ = v_patType_x3f_4479_;
v___y_4424_ = v___y_4486_;
v___y_4425_ = v___y_4483_;
v___y_4426_ = v___y_4480_;
v___y_4427_ = v___y_4481_;
v___y_4428_ = v_rhs_4488_;
v___y_4429_ = v_otherwise_x3f_4495_;
v___y_4430_ = v___y_4485_;
v___y_4431_ = v___y_4482_;
v___y_4432_ = v___x_4498_;
goto v___jp_4421_;
}
else
{
lean_object* v_val_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
v_val_4499_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4497_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_val_4499_);
lean_dec(v___x_4497_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_val_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
v___y_4422_ = v___y_4484_;
v___y_4423_ = v_patType_x3f_4479_;
v___y_4424_ = v___y_4486_;
v___y_4425_ = v___y_4483_;
v___y_4426_ = v___y_4480_;
v___y_4427_ = v___y_4481_;
v___y_4428_ = v_rhs_4488_;
v___y_4429_ = v_otherwise_x3f_4495_;
v___y_4430_ = v___y_4485_;
v___y_4431_ = v___y_4482_;
v___y_4432_ = v___x_4504_;
goto v___jp_4421_;
}
}
}
}
}
else
{
lean_object* v___x_4507_; 
lean_dec(v___x_4490_);
v___x_4507_ = lean_box(0);
v___y_4393_ = v___y_4486_;
v___y_4394_ = v___y_4484_;
v___y_4395_ = v___y_4482_;
v___y_4396_ = v___y_4481_;
v___y_4397_ = v___x_4507_;
v___y_4398_ = v_patType_x3f_4479_;
v___y_4399_ = v___y_4480_;
v___y_4400_ = v___y_4483_;
v___y_4401_ = v_rhs_4488_;
v___y_4402_ = v___y_4485_;
v___y_4403_ = v___x_4507_;
goto v___jp_4392_;
}
}
}
else
{
lean_object* v_pattern_4519_; lean_object* v___x_4520_; lean_object* v_patType_x3f_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v_pattern_4519_ = l_Lean_Syntax_getArg(v___x_4389_, v___x_4388_);
v___x_4520_ = lean_unsigned_to_nat(1u);
v___x_4577_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4520_);
v___x_4578_ = l_Lean_Syntax_isNone(v___x_4577_);
if (v___x_4578_ == 0)
{
uint8_t v___x_4579_; 
lean_inc(v___x_4577_);
v___x_4579_ = l_Lean_Syntax_matchesNull(v___x_4577_, v___x_4520_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
lean_dec(v___x_4577_);
lean_dec(v_pattern_4519_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4580_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; 
v___x_4581_ = l_Lean_Syntax_getArg(v___x_4577_, v___x_4388_);
lean_dec(v___x_4577_);
v___x_4582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4581_);
v___x_4583_ = l_Lean_Syntax_isOfKind(v___x_4581_, v___x_4582_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; 
lean_dec(v___x_4581_);
lean_dec(v_pattern_4519_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4584_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4584_;
}
else
{
lean_object* v_patType_x3f_4585_; lean_object* v___x_4586_; 
v_patType_x3f_4585_ = l_Lean_Syntax_getArg(v___x_4581_, v___x_4520_);
lean_dec(v___x_4581_);
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v_patType_x3f_4585_);
v_patType_x3f_4522_ = v___x_4586_;
v___y_4523_ = v_a_4372_;
v___y_4524_ = v_a_4373_;
v___y_4525_ = v_a_4374_;
v___y_4526_ = v_a_4375_;
v___y_4527_ = v_a_4376_;
v___y_4528_ = v_a_4377_;
v___y_4529_ = v_a_4378_;
goto v___jp_4521_;
}
}
}
else
{
lean_object* v___x_4587_; 
lean_dec(v___x_4577_);
v___x_4587_ = lean_box(0);
v_patType_x3f_4522_ = v___x_4587_;
v___y_4523_ = v_a_4372_;
v___y_4524_ = v_a_4373_;
v___y_4525_ = v_a_4374_;
v___y_4526_ = v_a_4375_;
v___y_4527_ = v_a_4376_;
v___y_4528_ = v_a_4377_;
v___y_4529_ = v_a_4378_;
goto v___jp_4521_;
}
v___jp_4521_:
{
lean_object* v___x_4530_; lean_object* v_rhs_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4530_ = lean_unsigned_to_nat(3u);
v_rhs_4531_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4530_);
v___x_4532_ = lean_unsigned_to_nat(4u);
v___x_4533_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4532_);
lean_dec(v_stx_4369_);
lean_inc(v___x_4533_);
v___x_4534_ = l_Lean_Syntax_matchesNull(v___x_4533_, v___x_4388_);
if (v___x_4534_ == 0)
{
uint8_t v___x_4535_; 
lean_dec(v_pattern_4519_);
v___x_4535_ = l_Lean_Syntax_isNone(v___x_4533_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
lean_inc(v___x_4533_);
v___x_4536_ = l_Lean_Syntax_matchesNull(v___x_4533_, v___x_4530_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_dec(v___x_4533_);
lean_dec(v_rhs_4531_);
lean_dec(v_patType_x3f_4522_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_letOrReassign_4368_);
v___x_4537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; lean_object* v_otherwise_x3f_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4538_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4539_ = l_Lean_Syntax_getArg(v___x_4533_, v___x_4520_);
v___x_4540_ = l_Lean_Syntax_getArg(v___x_4533_, v___x_4538_);
lean_dec(v___x_4533_);
v___x_4541_ = l_Lean_Syntax_getOptional_x3f(v___x_4540_);
lean_dec(v___x_4540_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_box(0);
v___y_4465_ = v___y_4523_;
v___y_4466_ = v___y_4526_;
v___y_4467_ = v___y_4529_;
v___y_4468_ = v___y_4528_;
v___y_4469_ = v_otherwise_x3f_4539_;
v___y_4470_ = v___y_4527_;
v___y_4471_ = v___y_4525_;
v___y_4472_ = v_patType_x3f_4522_;
v___y_4473_ = v___y_4524_;
v___y_4474_ = v_rhs_4531_;
v___y_4475_ = v___x_4542_;
goto v___jp_4464_;
}
else
{
lean_object* v_val_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_val_4543_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4541_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_val_4543_);
lean_dec(v___x_4541_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_val_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
v___y_4465_ = v___y_4523_;
v___y_4466_ = v___y_4526_;
v___y_4467_ = v___y_4529_;
v___y_4468_ = v___y_4528_;
v___y_4469_ = v_otherwise_x3f_4539_;
v___y_4470_ = v___y_4527_;
v___y_4471_ = v___y_4525_;
v___y_4472_ = v_patType_x3f_4522_;
v___y_4473_ = v___y_4524_;
v___y_4474_ = v_rhs_4531_;
v___y_4475_ = v___x_4548_;
goto v___jp_4464_;
}
}
}
}
}
else
{
lean_object* v___x_4551_; 
lean_dec(v___x_4533_);
v___x_4551_ = lean_box(0);
v___y_4435_ = v___y_4526_;
v___y_4436_ = v_patType_x3f_4522_;
v___y_4437_ = v___x_4551_;
v___y_4438_ = v___y_4523_;
v___y_4439_ = v_rhs_4531_;
v___y_4440_ = v___y_4528_;
v___y_4441_ = v___y_4525_;
v___y_4442_ = v___y_4529_;
v___y_4443_ = v___y_4527_;
v___y_4444_ = v___y_4524_;
v___y_4445_ = v___x_4551_;
goto v___jp_4434_;
}
}
else
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v___x_4533_);
lean_dec(v___x_4389_);
lean_dec(v_letOrReassign_4368_);
v___x_4552_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4553_ = l_Lean_Core_mkFreshUserName(v___x_4552_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4555_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4371_, v_tk_4370_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; uint8_t v_kind_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
v_kind_4557_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*3);
v___x_4558_ = l_Lean_mkIdentFrom(v_pattern_4519_, v_a_4554_, v___x_4384_);
lean_dec(v_pattern_4519_);
v___x_4559_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4559_, 0, v_a_4556_);
v___x_4560_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4558_, v_patType_x3f_4522_, v_rhs_4531_, v___x_4559_, v_kind_4557_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v___x_4560_;
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec(v_a_4554_);
lean_dec(v_rhs_4531_);
lean_dec(v_patType_x3f_4522_);
lean_dec(v_pattern_4519_);
v_a_4561_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4555_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4555_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v_rhs_4531_);
lean_dec(v_patType_x3f_4522_);
lean_dec(v_pattern_4519_);
lean_dec_ref(v_dec_4371_);
v_a_4569_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4553_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4553_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
}
v___jp_4392_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4405_ = l_Lean_Core_mkFreshUserName(v___x_4404_, v___y_4402_, v___y_4393_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___y_4410_; uint8_t v___x_4411_; lean_object* v___x_4412_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = l_Lean_mkIdentFrom(v___x_4389_, v_a_4406_, v___x_4391_);
v___x_4408_ = lean_box(v___x_4391_);
v___x_4409_ = lean_box(v___x_4386_);
lean_inc(v___x_4407_);
v___y_4410_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4410_, 0, v_letOrReassign_4368_);
lean_closure_set(v___y_4410_, 1, v___y_4397_);
lean_closure_set(v___y_4410_, 2, v___x_4408_);
lean_closure_set(v___y_4410_, 3, v___x_4380_);
lean_closure_set(v___y_4410_, 4, v___x_4381_);
lean_closure_set(v___y_4410_, 5, v___x_4382_);
lean_closure_set(v___y_4410_, 6, v___x_4389_);
lean_closure_set(v___y_4410_, 7, v___x_4407_);
lean_closure_set(v___y_4410_, 8, v_dec_4371_);
lean_closure_set(v___y_4410_, 9, v___x_4409_);
lean_closure_set(v___y_4410_, 10, v___y_4403_);
lean_closure_set(v___y_4410_, 11, v___x_4388_);
v___x_4411_ = 0;
v___x_4412_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4407_, v___y_4398_, v___y_4401_, v___y_4410_, v___x_4411_, v___y_4399_, v___y_4396_, v___y_4395_, v___y_4400_, v___y_4394_, v___y_4402_, v___y_4393_);
return v___x_4412_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v___y_4403_);
lean_dec(v___y_4401_);
lean_dec(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_letOrReassign_4368_);
v_a_4413_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4405_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4405_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
v___jp_4421_:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___y_4429_);
v___y_4393_ = v___y_4424_;
v___y_4394_ = v___y_4422_;
v___y_4395_ = v___y_4431_;
v___y_4396_ = v___y_4427_;
v___y_4397_ = v___x_4433_;
v___y_4398_ = v___y_4423_;
v___y_4399_ = v___y_4426_;
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___y_4428_;
v___y_4402_ = v___y_4430_;
v___y_4403_ = v___y_4432_;
goto v___jp_4392_;
}
v___jp_4434_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4447_ = l_Lean_Core_mkFreshUserName(v___x_4446_, v___y_4440_, v___y_4442_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___y_4453_; uint8_t v___x_4454_; lean_object* v___x_4455_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4447_);
v___x_4449_ = l_Lean_mkIdentFrom(v___x_4389_, v_a_4448_, v___x_4384_);
v___x_4450_ = lean_box(v___x_4384_);
v___x_4451_ = lean_box(v___x_4386_);
v___x_4452_ = lean_box(v___x_4391_);
lean_inc(v___x_4449_);
v___y_4453_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4453_, 0, v_letOrReassign_4368_);
lean_closure_set(v___y_4453_, 1, v___y_4437_);
lean_closure_set(v___y_4453_, 2, v___x_4450_);
lean_closure_set(v___y_4453_, 3, v___x_4380_);
lean_closure_set(v___y_4453_, 4, v___x_4381_);
lean_closure_set(v___y_4453_, 5, v___x_4382_);
lean_closure_set(v___y_4453_, 6, v___x_4389_);
lean_closure_set(v___y_4453_, 7, v___x_4449_);
lean_closure_set(v___y_4453_, 8, v_dec_4371_);
lean_closure_set(v___y_4453_, 9, v___x_4451_);
lean_closure_set(v___y_4453_, 10, v___y_4445_);
lean_closure_set(v___y_4453_, 11, v___x_4388_);
lean_closure_set(v___y_4453_, 12, v___x_4452_);
v___x_4454_ = 0;
v___x_4455_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4449_, v___y_4436_, v___y_4439_, v___y_4453_, v___x_4454_, v___y_4438_, v___y_4444_, v___y_4441_, v___y_4435_, v___y_4443_, v___y_4440_, v___y_4442_);
return v___x_4455_;
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v___y_4445_);
lean_dec(v___y_4439_);
lean_dec(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec(v___x_4389_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_letOrReassign_4368_);
v_a_4456_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4447_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4447_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
v___jp_4464_:
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___y_4469_);
v___y_4435_ = v___y_4466_;
v___y_4436_ = v___y_4472_;
v___y_4437_ = v___x_4476_;
v___y_4438_ = v___y_4465_;
v___y_4439_ = v___y_4474_;
v___y_4440_ = v___y_4468_;
v___y_4441_ = v___y_4471_;
v___y_4442_ = v___y_4467_;
v___y_4443_ = v___y_4470_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4475_;
goto v___jp_4434_;
}
}
}
else
{
lean_object* v___x_4588_; lean_object* v_x_4589_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v_xType_x3f_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v_xType_x3f_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v_x_4589_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4588_);
v___x_4662_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4589_);
v___x_4663_ = l_Lean_Syntax_isOfKind(v_x_4589_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; 
lean_dec(v_x_4589_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4664_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4664_;
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4665_ = lean_unsigned_to_nat(1u);
v___x_4666_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4665_);
v___x_4667_ = l_Lean_Syntax_isNone(v___x_4666_);
if (v___x_4667_ == 0)
{
uint8_t v___x_4668_; 
lean_inc(v___x_4666_);
v___x_4668_ = l_Lean_Syntax_matchesNull(v___x_4666_, v___x_4665_);
if (v___x_4668_ == 0)
{
lean_object* v___x_4669_; 
lean_dec(v___x_4666_);
lean_dec(v_x_4589_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4669_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4669_;
}
else
{
lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4670_ = l_Lean_Syntax_getArg(v___x_4666_, v___x_4588_);
lean_dec(v___x_4666_);
v___x_4671_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4670_);
v___x_4672_ = l_Lean_Syntax_isOfKind(v___x_4670_, v___x_4671_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
lean_dec(v___x_4670_);
lean_dec(v_x_4589_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v___x_4673_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4673_;
}
else
{
lean_object* v_xType_x3f_4674_; lean_object* v___x_4675_; 
v_xType_x3f_4674_ = l_Lean_Syntax_getArg(v___x_4670_, v___x_4665_);
lean_dec(v___x_4670_);
v___x_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_xType_x3f_4674_);
v_xType_x3f_4607_ = v___x_4675_;
v___y_4608_ = v_a_4372_;
v___y_4609_ = v_a_4373_;
v___y_4610_ = v_a_4374_;
v___y_4611_ = v_a_4375_;
v___y_4612_ = v_a_4376_;
v___y_4613_ = v_a_4377_;
v___y_4614_ = v_a_4378_;
goto v___jp_4606_;
}
}
}
else
{
lean_object* v___x_4676_; 
lean_dec(v___x_4666_);
v___x_4676_ = lean_box(0);
v_xType_x3f_4607_ = v___x_4676_;
v___y_4608_ = v_a_4372_;
v___y_4609_ = v_a_4373_;
v___y_4610_ = v_a_4374_;
v___y_4611_ = v_a_4375_;
v___y_4612_ = v_a_4376_;
v___y_4613_ = v_a_4377_;
v___y_4614_ = v_a_4378_;
goto v___jp_4606_;
}
}
v___jp_4590_:
{
uint8_t v_kind_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_kind_4601_ = lean_ctor_get_uint8(v___y_4591_, sizeof(void*)*3);
v___x_4602_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4368_);
lean_dec(v_letOrReassign_4368_);
v___x_4603_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4603_, 0, v___y_4591_);
lean_inc(v_x_4589_);
v___x_4604_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4604_, 0, lean_box(0));
lean_closure_set(v___x_4604_, 1, v___x_4602_);
lean_closure_set(v___x_4604_, 2, v_x_4589_);
lean_closure_set(v___x_4604_, 3, v___x_4603_);
v___x_4605_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4589_, v_xType_x3f_4593_, v___y_4592_, v___x_4604_, v_kind_4601_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
return v___x_4605_;
}
v___jp_4606_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4615_ = lean_unsigned_to_nat(1u);
v___x_4616_ = lean_mk_empty_array_with_capacity(v___x_4615_);
lean_inc(v_x_4589_);
v___x_4617_ = lean_array_push(v___x_4616_, v_x_4589_);
v___x_4618_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4368_, v___x_4617_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
lean_dec_ref(v___x_4617_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v___x_4619_; 
lean_dec_ref(v___x_4618_);
v___x_4619_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4371_, v_tk_4370_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4621_; lean_object* v_rhs_4622_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v___x_4619_);
v___x_4621_ = lean_unsigned_to_nat(3u);
v_rhs_4622_ = l_Lean_Syntax_getArg(v_stx_4369_, v___x_4621_);
lean_dec(v_stx_4369_);
if (lean_obj_tag(v_letOrReassign_4368_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4607_) == 0)
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = l_Lean_TSyntax_getId(v_x_4589_);
v___x_4624_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4623_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref(v___x_4624_);
v___x_4626_ = l_Lean_LocalDecl_type(v_a_4625_);
lean_dec(v_a_4625_);
v___x_4627_ = l_Lean_Elab_Term_exprToSyntax(v___x_4626_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4629_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref(v___x_4627_);
v___x_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4629_, 0, v_a_4628_);
v___y_4591_ = v_a_4620_;
v___y_4592_ = v_rhs_4622_;
v_xType_x3f_4593_ = v___x_4629_;
v___y_4594_ = v___y_4608_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
goto v___jp_4590_;
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec(v_rhs_4622_);
lean_dec(v_a_4620_);
lean_dec(v_x_4589_);
v_a_4630_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4627_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4627_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_dec(v_rhs_4622_);
lean_dec(v_a_4620_);
lean_dec(v_x_4589_);
v_a_4638_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4624_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4624_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
else
{
v___y_4591_ = v_a_4620_;
v___y_4592_ = v_rhs_4622_;
v_xType_x3f_4593_ = v_xType_x3f_4607_;
v___y_4594_ = v___y_4608_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
goto v___jp_4590_;
}
}
else
{
v___y_4591_ = v_a_4620_;
v___y_4592_ = v_rhs_4622_;
v_xType_x3f_4593_ = v_xType_x3f_4607_;
v___y_4594_ = v___y_4608_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
goto v___jp_4590_;
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec(v_xType_x3f_4607_);
lean_dec(v_x_4589_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v_a_4646_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4619_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4619_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec(v_xType_x3f_4607_);
lean_dec(v_x_4589_);
lean_dec_ref(v_dec_4371_);
lean_dec(v_stx_4369_);
lean_dec(v_letOrReassign_4368_);
v_a_4654_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4618_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4618_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4677_, lean_object* v_stx_4678_, lean_object* v_tk_4679_, lean_object* v_dec_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4677_, v_stx_4678_, v_tk_4679_, v_dec_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_tk_4679_);
return v_res_4689_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4692_ = l_Lean_stringToMessageData(v___x_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4693_, lean_object* v_mutTk_x3f_4694_, lean_object* v_initConfig_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4694_) == 0)
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4693_, v_initConfig_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
return v___x_4703_;
}
else
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = l_Lean_Syntax_getArg(v_letConfigStx_4693_, v___x_4704_);
v___x_4706_ = l_Lean_Syntax_getArgs(v___x_4705_);
lean_dec(v___x_4705_);
v___x_4707_ = lean_array_get_size(v___x_4706_);
lean_dec_ref(v___x_4706_);
v___x_4708_ = lean_nat_dec_eq(v___x_4707_, v___x_4704_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec_ref(v_initConfig_4695_);
v___x_4709_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4710_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4693_, v___x_4709_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec(v_letConfigStx_4693_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
else
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4693_, v_initConfig_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
return v___x_4719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4720_, lean_object* v_mutTk_x3f_4721_, lean_object* v_initConfig_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4720_, v_mutTk_x3f_4721_, v_initConfig_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_mutTk_x3f_4721_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4731_, lean_object* v_mutTk_x3f_4732_, lean_object* v_initConfig_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4731_, v_mutTk_x3f_4732_, v_initConfig_4733_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4743_, lean_object* v_mutTk_x3f_4744_, lean_object* v_initConfig_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4743_, v_mutTk_x3f_4744_, v_initConfig_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec(v_mutTk_x3f_4744_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4768_, lean_object* v_dec_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v___x_4778_; uint8_t v___x_4779_; 
v___x_4778_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4768_);
v___x_4779_ = l_Lean_Syntax_isOfKind(v_stx_4768_, v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
lean_dec_ref(v_dec_4769_);
lean_dec(v_stx_4768_);
v___x_4780_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; lean_object* v_tk_4782_; lean_object* v_mutTk_x3f_4784_; lean_object* v___y_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v___x_4781_ = lean_unsigned_to_nat(0u);
v_tk_4782_ = l_Lean_Syntax_getArg(v_stx_4768_, v___x_4781_);
v___x_4815_ = lean_unsigned_to_nat(1u);
v___x_4816_ = l_Lean_Syntax_getArg(v_stx_4768_, v___x_4815_);
v___x_4817_ = l_Lean_Syntax_isNone(v___x_4816_);
if (v___x_4817_ == 0)
{
uint8_t v___x_4818_; 
lean_inc(v___x_4816_);
v___x_4818_ = l_Lean_Syntax_matchesNull(v___x_4816_, v___x_4815_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; 
lean_dec(v___x_4816_);
lean_dec(v_tk_4782_);
lean_dec_ref(v_dec_4769_);
lean_dec(v_stx_4768_);
v___x_4819_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4819_;
}
else
{
lean_object* v_mutTk_x3f_4820_; lean_object* v___x_4821_; 
v_mutTk_x3f_4820_ = l_Lean_Syntax_getArg(v___x_4816_, v___x_4781_);
lean_dec(v___x_4816_);
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v_mutTk_x3f_4820_);
v_mutTk_x3f_4784_ = v___x_4821_;
v___y_4785_ = v_a_4770_;
v___y_4786_ = v_a_4771_;
v___y_4787_ = v_a_4772_;
v___y_4788_ = v_a_4773_;
v___y_4789_ = v_a_4774_;
v___y_4790_ = v_a_4775_;
v___y_4791_ = v_a_4776_;
goto v___jp_4783_;
}
}
else
{
lean_object* v___x_4822_; 
lean_dec(v___x_4816_);
v___x_4822_ = lean_box(0);
v_mutTk_x3f_4784_ = v___x_4822_;
v___y_4785_ = v_a_4770_;
v___y_4786_ = v_a_4771_;
v___y_4787_ = v_a_4772_;
v___y_4788_ = v_a_4773_;
v___y_4789_ = v_a_4774_;
v___y_4790_ = v_a_4775_;
v___y_4791_ = v_a_4776_;
goto v___jp_4783_;
}
v___jp_4783_:
{
lean_object* v___x_4792_; lean_object* v_config_4793_; lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4792_ = lean_unsigned_to_nat(2u);
v_config_4793_ = l_Lean_Syntax_getArg(v_stx_4768_, v___x_4792_);
v___x_4794_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4793_);
v___x_4795_ = l_Lean_Syntax_isOfKind(v_config_4793_, v___x_4794_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
lean_dec(v_config_4793_);
lean_dec(v_mutTk_x3f_4784_);
lean_dec(v_tk_4782_);
lean_dec_ref(v_dec_4769_);
lean_dec(v_stx_4768_);
v___x_4796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v_decl_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4797_ = lean_unsigned_to_nat(3u);
v_decl_4798_ = l_Lean_Syntax_getArg(v_stx_4768_, v___x_4797_);
lean_dec(v_stx_4768_);
v___x_4799_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4798_);
v___x_4800_ = l_Lean_Syntax_isOfKind(v_decl_4798_, v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
lean_dec(v_decl_4798_);
lean_dec(v_config_4793_);
lean_dec(v_mutTk_x3f_4784_);
lean_dec(v_tk_4782_);
lean_dec_ref(v_dec_4769_);
v___x_4801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4801_;
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4803_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4793_, v_mutTk_x3f_4784_, v___x_4802_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v___x_4803_);
v___x_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4805_, 0, v_mutTk_x3f_4784_);
v___x_4806_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4804_, v___x_4805_, v_decl_4798_, v_tk_4782_, v_dec_4769_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
return v___x_4806_;
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec(v_decl_4798_);
lean_dec(v_mutTk_x3f_4784_);
lean_dec(v_tk_4782_);
lean_dec_ref(v_dec_4769_);
v_a_4807_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4803_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4803_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4823_, lean_object* v_dec_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Elab_Do_elabDoLet(v_stx_4823_, v_dec_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec_ref(v_a_4825_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4841_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4842_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4844_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4845_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4841_, v___x_4842_, v___x_4843_, v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4853_, lean_object* v_dec_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4853_);
v___x_4864_ = l_Lean_Syntax_isOfKind(v_stx_4853_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; 
lean_dec_ref(v_dec_4854_);
lean_dec(v_stx_4853_);
v___x_4865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4865_;
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v___x_4866_ = lean_unsigned_to_nat(1u);
v___x_4867_ = l_Lean_Syntax_getArg(v_stx_4853_, v___x_4866_);
v___x_4868_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4867_);
v___x_4869_ = l_Lean_Syntax_isOfKind(v___x_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; 
lean_dec(v___x_4867_);
lean_dec_ref(v_dec_4854_);
lean_dec(v_stx_4853_);
v___x_4870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4870_;
}
else
{
lean_object* v___x_4871_; lean_object* v_decl_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v___x_4871_ = lean_unsigned_to_nat(2u);
v_decl_4872_ = l_Lean_Syntax_getArg(v_stx_4853_, v___x_4871_);
v___x_4873_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4872_);
v___x_4874_ = l_Lean_Syntax_isOfKind(v_decl_4872_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; 
lean_dec(v_decl_4872_);
lean_dec(v___x_4867_);
lean_dec_ref(v_dec_4854_);
lean_dec(v_stx_4853_);
v___x_4875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4875_;
}
else
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4876_ = 0;
v___x_4877_ = lean_box(0);
v___x_4878_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1, v___x_4874_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1 + 1, v___x_4876_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1 + 2, v___x_4876_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1 + 3, v___x_4876_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1 + 4, v___x_4876_);
v___x_4879_ = l_Lean_Elab_Term_mkLetConfig(v___x_4867_, v___x_4878_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; lean_object* v_tk_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref(v___x_4879_);
v___x_4881_ = lean_unsigned_to_nat(0u);
v_tk_4882_ = l_Lean_Syntax_getArg(v_stx_4853_, v___x_4881_);
lean_dec(v_stx_4853_);
v___x_4883_ = lean_box(1);
v___x_4884_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4880_, v___x_4883_, v_decl_4872_, v_tk_4882_, v_dec_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
return v___x_4884_;
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v_decl_4872_);
lean_dec_ref(v_dec_4854_);
lean_dec(v_stx_4853_);
v_a_4885_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4879_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4879_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4893_, lean_object* v_dec_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Elab_Do_elabDoHave(v_stx_4893_, v_dec_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
lean_dec(v_a_4899_);
lean_dec_ref(v_a_4898_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec_ref(v_a_4895_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4911_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4912_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4913_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4914_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4915_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4911_, v___x_4912_, v___x_4913_, v___x_4914_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v_decls_4924_, lean_object* v_a_4925_, uint8_t v___x_4926_, lean_object* v_body_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v_ref_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v_ref_4936_ = lean_ctor_get(v___y_4933_, 5);
v___x_4937_ = 0;
v___x_4938_ = l_Lean_SourceInfo_fromRef(v_ref_4936_, v___x_4937_);
v___x_4939_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4940_ = l_Lean_Name_mkStr4(v___x_4920_, v___x_4921_, v___x_4922_, v___x_4939_);
v___x_4941_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4938_, 4);
v___x_4942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4938_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4938_);
lean_ctor_set(v___x_4944_, 1, v___x_4943_);
v___x_4945_ = l_Lean_Syntax_node2(v___x_4938_, v___x_4923_, v___x_4942_, v___x_4944_);
v___x_4946_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4938_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = l_Lean_Syntax_node4(v___x_4938_, v___x_4940_, v___x_4945_, v_decls_4924_, v___x_4947_, v_body_4927_);
v___x_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4949_, 0, v_a_4925_);
v___x_4950_ = l_Lean_Elab_Term_elabTerm(v___x_4948_, v___x_4949_, v___x_4926_, v___x_4926_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v_decls_4955_, lean_object* v_a_4956_, lean_object* v___x_4957_, lean_object* v_body_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
uint8_t v___x_5030__boxed_4967_; lean_object* v_res_4968_; 
v___x_5030__boxed_4967_ = lean_unbox(v___x_4957_);
v_res_4968_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4951_, v___x_4952_, v___x_4953_, v___x_4954_, v_decls_4955_, v_a_4956_, v___x_5030__boxed_4967_, v_body_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec_ref(v___y_4959_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
if (lean_obj_tag(v_a_4969_) == 0)
{
lean_object* v___x_4971_; 
v___x_4971_ = l_List_reverse___redArg(v_a_4970_);
return v___x_4971_;
}
else
{
lean_object* v_head_4972_; lean_object* v_tail_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4982_; 
v_head_4972_ = lean_ctor_get(v_a_4969_, 0);
v_tail_4973_ = lean_ctor_get(v_a_4969_, 1);
v_isSharedCheck_4982_ = !lean_is_exclusive(v_a_4969_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4975_ = v_a_4969_;
v_isShared_4976_ = v_isSharedCheck_4982_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_tail_4973_);
lean_inc(v_head_4972_);
lean_dec(v_a_4969_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4982_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4977_ = l_Lean_MessageData_ofSyntax(v_head_4972_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v_a_4970_);
lean_ctor_set(v___x_4975_, 0, v___x_4977_);
v___x_4979_ = v___x_4975_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_a_4970_);
v___x_4979_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
v_a_4969_ = v_tail_4973_;
v_a_4970_ = v___x_4979_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_5000_ = l_Lean_stringToMessageData(v___x_4999_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_5001_, lean_object* v_dec_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5011_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5012_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5013_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5014_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_5001_);
v___x_5015_ = l_Lean_Syntax_isOfKind(v_stx_5001_, v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; 
lean_dec_ref(v_dec_5002_);
lean_dec(v_stx_5001_);
v___x_5016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5016_;
}
else
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5017_ = lean_unsigned_to_nat(0u);
v___x_5018_ = l_Lean_Syntax_getArg(v_stx_5001_, v___x_5017_);
v___x_5019_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5018_);
v___x_5020_ = l_Lean_Syntax_isOfKind(v___x_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_5002_);
lean_dec(v_stx_5001_);
v___x_5021_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v_decls_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5022_ = lean_unsigned_to_nat(1u);
v_decls_5023_ = l_Lean_Syntax_getArg(v_stx_5001_, v___x_5022_);
lean_dec(v_stx_5001_);
v___x_5024_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5023_);
v___x_5025_ = l_Lean_Syntax_isOfKind(v_decls_5023_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
lean_dec(v_decls_5023_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_5002_);
v___x_5026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5026_;
}
else
{
lean_object* v_tk_5027_; lean_object* v___x_5028_; 
v_tk_5027_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5017_);
lean_dec(v___x_5018_);
v___x_5028_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5002_, v_tk_5027_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
lean_dec(v_tk_5027_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___x_5028_);
lean_inc(v_decls_5023_);
v___x_5030_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5023_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v_doBlockResultType_5032_; lean_object* v___x_5033_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref(v___x_5030_);
v_doBlockResultType_5032_ = lean_ctor_get(v_a_5003_, 3);
lean_inc_ref(v_doBlockResultType_5032_);
v___x_5033_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_5032_, v_a_5003_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5035_; lean_object* v___f_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
v___x_5035_ = lean_box(v___x_5025_);
v___f_5036_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5036_, 0, v___x_5011_);
lean_closure_set(v___f_5036_, 1, v___x_5012_);
lean_closure_set(v___f_5036_, 2, v___x_5013_);
lean_closure_set(v___f_5036_, 3, v___x_5019_);
lean_closure_set(v___f_5036_, 4, v_decls_5023_);
lean_closure_set(v___f_5036_, 5, v_a_5034_);
lean_closure_set(v___f_5036_, 6, v___x_5035_);
v___x_5037_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5038_ = lean_array_to_list(v_a_5031_);
v___x_5039_ = lean_box(0);
v___x_5040_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5038_, v___x_5039_);
v___x_5041_ = l_Lean_MessageData_ofList(v___x_5040_);
v___x_5042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5037_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5043_, 0, v_a_5029_);
v___x_5044_ = lean_box(0);
v___x_5045_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5042_, v___x_5043_, v___f_5036_, v___x_5044_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
return v___x_5045_;
}
else
{
lean_dec(v_a_5031_);
lean_dec(v_a_5029_);
lean_dec(v_decls_5023_);
return v___x_5033_;
}
}
else
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
lean_dec(v_a_5029_);
lean_dec(v_decls_5023_);
v_a_5046_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_5030_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5030_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_dec(v_decls_5023_);
v_a_5054_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_5028_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5028_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5062_, lean_object* v_dec_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5062_, v_dec_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec_ref(v_a_5064_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5080_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5081_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5082_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5083_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5084_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5080_, v___x_5081_, v___x_5082_, v___x_5083_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5100_, lean_object* v_dec_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v___y_5111_; uint8_t v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___x_5143_; uint8_t v___x_5144_; 
v___x_5143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_5100_);
v___x_5144_ = l_Lean_Syntax_isOfKind(v_stx_5100_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; 
lean_dec_ref(v_dec_5101_);
lean_dec(v_stx_5100_);
v___x_5145_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5145_;
}
else
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; 
v___x_5146_ = lean_unsigned_to_nat(0u);
v___x_5147_ = l_Lean_Syntax_getArg(v_stx_5100_, v___x_5146_);
lean_dec(v_stx_5100_);
v___x_5148_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5147_);
v___x_5149_ = l_Lean_Syntax_isOfKind(v___x_5147_, v___x_5148_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; uint8_t v___x_5151_; 
v___x_5150_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5147_);
v___x_5151_ = l_Lean_Syntax_isOfKind(v___x_5147_, v___x_5150_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; 
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5152_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5152_;
}
else
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v_decl_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5153_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5154_ = lean_unsigned_to_nat(1u);
v___x_5155_ = lean_mk_empty_array_with_capacity(v___x_5154_);
v___x_5156_ = lean_array_push(v___x_5155_, v___x_5147_);
v___x_5157_ = lean_box(2);
v_decl_5158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5158_, 0, v___x_5157_);
lean_ctor_set(v_decl_5158_, 1, v___x_5153_);
lean_ctor_set(v_decl_5158_, 2, v___x_5156_);
v___x_5159_ = lean_box(0);
v___x_5160_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5160_, 0, v___x_5159_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1, v___x_5149_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1 + 1, v___x_5149_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1 + 2, v___x_5149_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1 + 3, v___x_5149_);
lean_ctor_set_uint8(v___x_5160_, sizeof(void*)*1 + 4, v___x_5149_);
v___x_5161_ = lean_box(2);
lean_inc_ref(v_decl_5158_);
v___x_5162_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5160_, v___x_5161_, v_decl_5158_, v_decl_5158_, v_dec_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_);
return v___x_5162_;
}
}
else
{
lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = l_Lean_Syntax_getArg(v___x_5147_, v___x_5146_);
v___x_5164_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5163_);
v___x_5165_ = l_Lean_Syntax_isOfKind(v___x_5163_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
lean_dec(v___x_5163_);
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5166_;
}
else
{
lean_object* v___x_5167_; lean_object* v_xType_x3f_5169_; lean_object* v___y_5170_; lean_object* v___y_5171_; lean_object* v___y_5172_; lean_object* v___y_5173_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5167_ = l_Lean_Syntax_getArg(v___x_5163_, v___x_5146_);
lean_dec(v___x_5163_);
v___x_5196_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5167_);
v___x_5197_ = l_Lean_Syntax_isOfKind(v___x_5167_, v___x_5196_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; 
lean_dec(v___x_5167_);
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5198_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5198_;
}
else
{
lean_object* v___x_5199_; lean_object* v___x_5200_; uint8_t v___x_5201_; 
v___x_5199_ = lean_unsigned_to_nat(1u);
v___x_5200_ = l_Lean_Syntax_getArg(v___x_5147_, v___x_5199_);
v___x_5201_ = l_Lean_Syntax_matchesNull(v___x_5200_, v___x_5146_);
if (v___x_5201_ == 0)
{
lean_object* v___x_5202_; 
lean_dec(v___x_5167_);
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5202_;
}
else
{
lean_object* v___x_5203_; lean_object* v___x_5204_; uint8_t v___x_5205_; 
v___x_5203_ = lean_unsigned_to_nat(2u);
v___x_5204_ = l_Lean_Syntax_getArg(v___x_5147_, v___x_5203_);
v___x_5205_ = l_Lean_Syntax_isNone(v___x_5204_);
if (v___x_5205_ == 0)
{
uint8_t v___x_5206_; 
lean_inc(v___x_5204_);
v___x_5206_ = l_Lean_Syntax_matchesNull(v___x_5204_, v___x_5199_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5207_; 
lean_dec(v___x_5204_);
lean_dec(v___x_5167_);
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5207_;
}
else
{
lean_object* v___x_5208_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5208_ = l_Lean_Syntax_getArg(v___x_5204_, v___x_5146_);
lean_dec(v___x_5204_);
v___x_5209_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5208_);
v___x_5210_ = l_Lean_Syntax_isOfKind(v___x_5208_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
lean_dec(v___x_5208_);
lean_dec(v___x_5167_);
lean_dec(v___x_5147_);
lean_dec_ref(v_dec_5101_);
v___x_5211_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5211_;
}
else
{
lean_object* v_xType_x3f_5212_; lean_object* v___x_5213_; 
v_xType_x3f_5212_ = l_Lean_Syntax_getArg(v___x_5208_, v___x_5199_);
lean_dec(v___x_5208_);
v___x_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5213_, 0, v_xType_x3f_5212_);
v_xType_x3f_5169_ = v___x_5213_;
v___y_5170_ = v_a_5102_;
v___y_5171_ = v_a_5103_;
v___y_5172_ = v_a_5104_;
v___y_5173_ = v_a_5105_;
v___y_5174_ = v_a_5106_;
v___y_5175_ = v_a_5107_;
v___y_5176_ = v_a_5108_;
goto v___jp_5168_;
}
}
}
else
{
lean_object* v___x_5214_; 
lean_dec(v___x_5204_);
v___x_5214_ = lean_box(0);
v_xType_x3f_5169_ = v___x_5214_;
v___y_5170_ = v_a_5102_;
v___y_5171_ = v_a_5103_;
v___y_5172_ = v_a_5104_;
v___y_5173_ = v_a_5105_;
v___y_5174_ = v_a_5106_;
v___y_5175_ = v_a_5107_;
v___y_5176_ = v_a_5108_;
goto v___jp_5168_;
}
}
}
v___jp_5168_:
{
lean_object* v_ref_5177_; lean_object* v___x_5178_; lean_object* v_tk_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; uint8_t v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v_ref_5177_ = lean_ctor_get(v___y_5175_, 5);
v___x_5178_ = lean_unsigned_to_nat(3u);
v_tk_5179_ = l_Lean_Syntax_getArg(v___x_5147_, v___x_5178_);
v___x_5180_ = lean_unsigned_to_nat(4u);
v___x_5181_ = l_Lean_Syntax_getArg(v___x_5147_, v___x_5180_);
lean_dec(v___x_5147_);
v___x_5182_ = 0;
v___x_5183_ = l_Lean_SourceInfo_fromRef(v_ref_5177_, v___x_5182_);
v___x_5184_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5183_, 2);
v___x_5185_ = l_Lean_Syntax_node1(v___x_5183_, v___x_5164_, v___x_5167_);
v___x_5186_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5187_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5183_);
lean_ctor_set(v___x_5188_, 1, v___x_5186_);
lean_ctor_set(v___x_5188_, 2, v___x_5187_);
if (lean_obj_tag(v_xType_x3f_5169_) == 1)
{
lean_object* v_val_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v_val_5189_ = lean_ctor_get(v_xType_x3f_5169_, 0);
lean_inc(v_val_5189_);
lean_dec_ref(v_xType_x3f_5169_);
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5183_, 2);
v___x_5192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5183_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l_Lean_Syntax_node2(v___x_5183_, v___x_5190_, v___x_5192_, v_val_5189_);
v___x_5194_ = l_Array_mkArray1___redArg(v___x_5193_);
v___y_5111_ = v___y_5173_;
v___y_5112_ = v___x_5182_;
v___y_5113_ = v___x_5188_;
v___y_5114_ = v_tk_5179_;
v___y_5115_ = v___y_5171_;
v___y_5116_ = v___x_5181_;
v___y_5117_ = v___y_5176_;
v___y_5118_ = v___x_5183_;
v___y_5119_ = v___y_5174_;
v___y_5120_ = v___x_5184_;
v___y_5121_ = v___x_5185_;
v___y_5122_ = v___y_5175_;
v___y_5123_ = v___x_5187_;
v___y_5124_ = v___x_5186_;
v___y_5125_ = v___y_5172_;
v___y_5126_ = v___y_5170_;
v___y_5127_ = v___x_5194_;
goto v___jp_5110_;
}
else
{
lean_object* v___x_5195_; 
lean_dec(v_xType_x3f_5169_);
v___x_5195_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_5111_ = v___y_5173_;
v___y_5112_ = v___x_5182_;
v___y_5113_ = v___x_5188_;
v___y_5114_ = v_tk_5179_;
v___y_5115_ = v___y_5171_;
v___y_5116_ = v___x_5181_;
v___y_5117_ = v___y_5176_;
v___y_5118_ = v___x_5183_;
v___y_5119_ = v___y_5174_;
v___y_5120_ = v___x_5184_;
v___y_5121_ = v___x_5185_;
v___y_5122_ = v___y_5175_;
v___y_5123_ = v___x_5187_;
v___y_5124_ = v___x_5186_;
v___y_5125_ = v___y_5172_;
v___y_5126_ = v___y_5170_;
v___y_5127_ = v___x_5195_;
goto v___jp_5110_;
}
}
}
}
}
v___jp_5110_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
lean_inc_ref(v___y_5123_);
v___x_5128_ = l_Array_append___redArg(v___y_5123_, v___y_5127_);
lean_dec_ref(v___y_5127_);
lean_inc(v___y_5124_);
lean_inc_n(v___y_5118_, 2);
v___x_5129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5129_, 0, v___y_5118_);
lean_ctor_set(v___x_5129_, 1, v___y_5124_);
lean_ctor_set(v___x_5129_, 2, v___x_5128_);
v___x_5130_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5131_, 0, v___y_5118_);
lean_ctor_set(v___x_5131_, 1, v___x_5130_);
lean_inc(v___y_5120_);
v___x_5132_ = l_Lean_Syntax_node5(v___y_5118_, v___y_5120_, v___y_5121_, v___y_5113_, v___x_5129_, v___x_5131_, v___y_5116_);
v___x_5133_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = lean_mk_empty_array_with_capacity(v___x_5134_);
v___x_5136_ = lean_array_push(v___x_5135_, v___x_5132_);
v___x_5137_ = lean_box(2);
v___x_5138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
lean_ctor_set(v___x_5138_, 1, v___x_5133_);
lean_ctor_set(v___x_5138_, 2, v___x_5136_);
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5140_, 0, v___x_5139_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1, v___y_5112_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 1, v___y_5112_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 2, v___y_5112_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 3, v___y_5112_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*1 + 4, v___y_5112_);
v___x_5141_ = lean_box(2);
v___x_5142_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5140_, v___x_5141_, v___x_5138_, v___y_5114_, v_dec_5101_, v___y_5126_, v___y_5115_, v___y_5125_, v___y_5111_, v___y_5119_, v___y_5122_, v___y_5117_);
return v___x_5142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5215_, lean_object* v_dec_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5215_, v_dec_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec_ref(v_a_5217_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5233_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5236_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5237_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5233_, v___x_5234_, v___x_5235_, v___x_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
uint8_t v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5249_ = 0;
v___x_5250_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5240_, v___x_5249_);
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v_____do__lift_5252_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5281_, size_t v_sz_5282_, size_t v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_){
_start:
{
uint8_t v___x_5287_; 
v___x_5287_ = lean_usize_dec_lt(v_i_5283_, v_sz_5282_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; 
v___x_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5288_, 0, v_b_5284_);
return v___x_5288_;
}
else
{
lean_object* v_ref_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v_a_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; size_t v___x_5326_; size_t v___x_5327_; 
v_ref_5289_ = lean_ctor_get(v___y_5285_, 5);
v___x_5290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5292_ = lean_array_uget_borrowed(v_as_5281_, v_i_5283_);
v___x_5293_ = 0;
v___x_5294_ = l_Lean_SourceInfo_fromRef(v_ref_5289_, v___x_5293_);
v___x_5295_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5297_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5298_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5294_, 17);
v___x_5299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5294_);
lean_ctor_set(v___x_5299_, 1, v___x_5298_);
v___x_5300_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5294_);
lean_ctor_set(v___x_5301_, 1, v___x_5300_);
v___x_5302_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5295_, v___x_5301_);
v___x_5303_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5304_, 0, v___x_5294_);
lean_ctor_set(v___x_5304_, 1, v___x_5295_);
lean_ctor_set(v___x_5304_, 2, v___x_5303_);
lean_inc_ref_n(v___x_5304_, 3);
v___x_5305_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5290_, v___x_5304_);
v___x_5306_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5307_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5308_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5292_, 2);
v___x_5309_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5308_, v_a_5292_);
v___x_5310_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5294_);
lean_ctor_set(v___x_5311_, 1, v___x_5310_);
v___x_5312_ = l_Lean_Syntax_node5(v___x_5294_, v___x_5307_, v___x_5309_, v___x_5304_, v___x_5304_, v___x_5311_, v_a_5292_);
v___x_5313_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5306_, v___x_5312_);
v___x_5314_ = l_Lean_Syntax_node4(v___x_5294_, v___x_5297_, v___x_5299_, v___x_5302_, v___x_5305_, v___x_5313_);
v___x_5315_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5294_);
lean_ctor_set(v___x_5316_, 1, v___x_5315_);
v___x_5317_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5295_, v___x_5316_);
v___x_5318_ = l_Lean_Syntax_node2(v___x_5294_, v___x_5296_, v___x_5314_, v___x_5317_);
v___x_5319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5294_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = l_Lean_Syntax_node2(v___x_5294_, v___x_5319_, v___x_5321_, v_b_5284_);
v___x_5323_ = l_Lean_Syntax_node2(v___x_5294_, v___x_5296_, v___x_5322_, v___x_5304_);
v___x_5324_ = l_Lean_Syntax_node2(v___x_5294_, v___x_5295_, v___x_5318_, v___x_5323_);
v___x_5325_ = l_Lean_Syntax_node1(v___x_5294_, v___x_5291_, v___x_5324_);
v___x_5326_ = ((size_t)1ULL);
v___x_5327_ = lean_usize_add(v_i_5283_, v___x_5326_);
v_i_5283_ = v___x_5327_;
v_b_5284_ = v___x_5325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5329_, lean_object* v_sz_5330_, lean_object* v_i_5331_, lean_object* v_b_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
size_t v_sz_boxed_5335_; size_t v_i_boxed_5336_; lean_object* v_res_5337_; 
v_sz_boxed_5335_ = lean_unbox_usize(v_sz_5330_);
lean_dec(v_sz_5330_);
v_i_boxed_5336_ = lean_unbox_usize(v_i_5331_);
lean_dec(v_i_5331_);
v_res_5337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5329_, v_sz_boxed_5335_, v_i_boxed_5336_, v_b_5332_, v___y_5333_);
lean_dec_ref(v___y_5333_);
lean_dec_ref(v_as_5329_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5338_, size_t v_sz_5339_, size_t v_i_5340_, lean_object* v_b_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
uint8_t v___x_5350_; 
v___x_5350_ = lean_usize_dec_lt(v_i_5340_, v_sz_5339_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
v___x_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5351_, 0, v_b_5341_);
return v___x_5351_;
}
else
{
lean_object* v_ref_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v_a_5355_; uint8_t v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; size_t v___x_5389_; size_t v___x_5390_; lean_object* v___x_5391_; 
v_ref_5352_ = lean_ctor_get(v___y_5347_, 5);
v___x_5353_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5355_ = lean_array_uget_borrowed(v_as_5338_, v_i_5340_);
v___x_5356_ = 0;
v___x_5357_ = l_Lean_SourceInfo_fromRef(v_ref_5352_, v___x_5356_);
v___x_5358_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5360_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5361_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5357_, 17);
v___x_5362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5357_);
lean_ctor_set(v___x_5362_, 1, v___x_5361_);
v___x_5363_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5364_, 0, v___x_5357_);
lean_ctor_set(v___x_5364_, 1, v___x_5363_);
v___x_5365_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5358_, v___x_5364_);
v___x_5366_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5357_);
lean_ctor_set(v___x_5367_, 1, v___x_5358_);
lean_ctor_set(v___x_5367_, 2, v___x_5366_);
lean_inc_ref_n(v___x_5367_, 3);
v___x_5368_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5353_, v___x_5367_);
v___x_5369_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5370_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5371_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5355_, 2);
v___x_5372_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5371_, v_a_5355_);
v___x_5373_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5357_);
lean_ctor_set(v___x_5374_, 1, v___x_5373_);
v___x_5375_ = l_Lean_Syntax_node5(v___x_5357_, v___x_5370_, v___x_5372_, v___x_5367_, v___x_5367_, v___x_5374_, v_a_5355_);
v___x_5376_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5369_, v___x_5375_);
v___x_5377_ = l_Lean_Syntax_node4(v___x_5357_, v___x_5360_, v___x_5362_, v___x_5365_, v___x_5368_, v___x_5376_);
v___x_5378_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5379_, 0, v___x_5357_);
lean_ctor_set(v___x_5379_, 1, v___x_5378_);
v___x_5380_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5358_, v___x_5379_);
v___x_5381_ = l_Lean_Syntax_node2(v___x_5357_, v___x_5359_, v___x_5377_, v___x_5380_);
v___x_5382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5357_);
lean_ctor_set(v___x_5384_, 1, v___x_5383_);
v___x_5385_ = l_Lean_Syntax_node2(v___x_5357_, v___x_5382_, v___x_5384_, v_b_5341_);
v___x_5386_ = l_Lean_Syntax_node2(v___x_5357_, v___x_5359_, v___x_5385_, v___x_5367_);
v___x_5387_ = l_Lean_Syntax_node2(v___x_5357_, v___x_5358_, v___x_5381_, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node1(v___x_5357_, v___x_5354_, v___x_5387_);
v___x_5389_ = ((size_t)1ULL);
v___x_5390_ = lean_usize_add(v_i_5340_, v___x_5389_);
v___x_5391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5338_, v_sz_5339_, v___x_5390_, v___x_5388_, v___y_5347_);
return v___x_5391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5392_, lean_object* v_sz_5393_, lean_object* v_i_5394_, lean_object* v_b_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
size_t v_sz_boxed_5404_; size_t v_i_boxed_5405_; lean_object* v_res_5406_; 
v_sz_boxed_5404_ = lean_unbox_usize(v_sz_5393_);
lean_dec(v_sz_5393_);
v_i_boxed_5405_ = lean_unbox_usize(v_i_5394_);
lean_dec(v_i_5394_);
v_res_5406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5392_, v_sz_boxed_5404_, v_i_boxed_5405_, v_b_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
lean_dec(v___y_5400_);
lean_dec_ref(v___y_5399_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec_ref(v_as_5392_);
return v_res_5406_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5447_ = l_String_toRawSubstring_x27(v___x_5446_);
return v___x_5447_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5461_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5462_ = l_String_toRawSubstring_x27(v___x_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5479_, lean_object* v_dec_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_){
_start:
{
lean_object* v___x_5489_; uint8_t v___x_5490_; 
v___x_5489_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5479_);
v___x_5490_ = l_Lean_Syntax_isOfKind(v_stx_5479_, v___x_5489_);
if (v___x_5490_ == 0)
{
lean_object* v___x_5491_; 
lean_dec_ref(v_dec_5480_);
lean_dec(v_stx_5479_);
v___x_5491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5491_;
}
else
{
lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; uint8_t v___y_5497_; lean_object* v_body_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; uint8_t v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; uint8_t v___y_5593_; lean_object* v_a_5594_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; uint8_t v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; lean_object* v___y_5618_; lean_object* v___y_5619_; lean_object* v___y_5620_; lean_object* v___y_5621_; lean_object* v_mutTk_x3f_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___x_5724_; lean_object* v___x_5725_; uint8_t v___x_5726_; 
v___x_5724_ = lean_unsigned_to_nat(1u);
v___x_5725_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5724_);
v___x_5726_ = l_Lean_Syntax_isNone(v___x_5725_);
if (v___x_5726_ == 0)
{
uint8_t v___x_5727_; 
lean_inc(v___x_5725_);
v___x_5727_ = l_Lean_Syntax_matchesNull(v___x_5725_, v___x_5724_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; 
lean_dec(v___x_5725_);
lean_dec_ref(v_dec_5480_);
lean_dec(v_stx_5479_);
v___x_5728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5728_;
}
else
{
lean_object* v___x_5729_; lean_object* v_mutTk_x3f_5730_; lean_object* v___x_5731_; 
v___x_5729_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5730_ = l_Lean_Syntax_getArg(v___x_5725_, v___x_5729_);
lean_dec(v___x_5725_);
v___x_5731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5731_, 0, v_mutTk_x3f_5730_);
v_mutTk_x3f_5693_ = v___x_5731_;
v___y_5694_ = v_a_5481_;
v___y_5695_ = v_a_5482_;
v___y_5696_ = v_a_5483_;
v___y_5697_ = v_a_5484_;
v___y_5698_ = v_a_5485_;
v___y_5699_ = v_a_5486_;
v___y_5700_ = v_a_5487_;
goto v___jp_5692_;
}
}
else
{
lean_object* v___x_5732_; 
lean_dec(v___x_5725_);
v___x_5732_ = lean_box(0);
v_mutTk_x3f_5693_ = v___x_5732_;
v___y_5694_ = v_a_5481_;
v___y_5695_ = v_a_5482_;
v___y_5696_ = v_a_5483_;
v___y_5697_ = v_a_5484_;
v___y_5698_ = v_a_5485_;
v___y_5699_ = v_a_5486_;
v___y_5700_ = v_a_5487_;
goto v___jp_5692_;
}
v___jp_5492_:
{
lean_object* v_eq_x3f_5506_; 
v_eq_x3f_5506_ = lean_ctor_get(v___y_5495_, 0);
lean_inc(v_eq_x3f_5506_);
lean_dec_ref(v___y_5495_);
if (lean_obj_tag(v_eq_x3f_5506_) == 1)
{
lean_object* v_val_5507_; lean_object* v_ref_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
v_val_5507_ = lean_ctor_get(v_eq_x3f_5506_, 0);
lean_inc(v_val_5507_);
lean_dec_ref(v_eq_x3f_5506_);
v_ref_5508_ = lean_ctor_get(v___y_5504_, 5);
v___x_5509_ = l_Lean_SourceInfo_fromRef(v_ref_5508_, v___y_5497_);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5511_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5509_, 19);
v___x_5512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5512_, 0, v___x_5509_);
lean_ctor_set(v___x_5512_, 1, v___x_5511_);
v___x_5513_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5514_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5509_);
lean_ctor_set(v___x_5515_, 1, v___x_5513_);
lean_ctor_set(v___x_5515_, 2, v___x_5514_);
v___x_5516_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5517_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5509_);
lean_ctor_set(v___x_5518_, 1, v___x_5517_);
v___x_5519_ = l_Lean_Syntax_node2(v___x_5509_, v___x_5513_, v_val_5507_, v___x_5518_);
v___x_5520_ = l_Lean_Syntax_node2(v___x_5509_, v___x_5516_, v___x_5519_, v___y_5496_);
v___x_5521_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5513_, v___x_5520_);
v___x_5522_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5509_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
v___x_5524_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5509_);
lean_ctor_set(v___x_5527_, 1, v___x_5526_);
v___x_5528_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5513_, v___y_5494_);
v___x_5529_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5513_, v___x_5528_);
v___x_5530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5509_);
lean_ctor_set(v___x_5531_, 1, v___x_5530_);
lean_inc_ref(v___x_5531_);
lean_inc_ref(v___x_5527_);
v___x_5532_ = l_Lean_Syntax_node4(v___x_5509_, v___x_5525_, v___x_5527_, v___x_5529_, v___x_5531_, v_body_5498_);
v___x_5533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5509_);
lean_ctor_set(v___x_5535_, 1, v___x_5534_);
v___x_5536_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5533_, v___x_5535_);
v___x_5537_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5513_, v___x_5536_);
v___x_5538_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5513_, v___x_5537_);
v___x_5539_ = l_Lean_Syntax_node4(v___x_5509_, v___x_5525_, v___x_5527_, v___x_5538_, v___x_5531_, v___y_5493_);
v___x_5540_ = l_Lean_Syntax_node2(v___x_5509_, v___x_5513_, v___x_5532_, v___x_5539_);
v___x_5541_ = l_Lean_Syntax_node1(v___x_5509_, v___x_5524_, v___x_5540_);
lean_inc_ref_n(v___x_5515_, 2);
v___x_5542_ = l_Lean_Syntax_node7(v___x_5509_, v___x_5510_, v___x_5512_, v___x_5515_, v___x_5515_, v___x_5515_, v___x_5521_, v___x_5523_, v___x_5541_);
v___x_5543_ = l_Lean_Elab_Do_elabDoElem(v___x_5542_, v_dec_5480_, v___x_5490_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
return v___x_5543_;
}
else
{
lean_object* v_ref_5544_; lean_object* v___x_5545_; lean_object* v_a_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
lean_dec(v_eq_x3f_5506_);
v_ref_5544_ = lean_ctor_get(v___y_5504_, 5);
v___x_5545_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5544_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc_n(v_a_5546_, 18);
lean_dec_ref(v___x_5545_);
v___x_5547_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5548_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5549_, 0, v_a_5546_);
lean_ctor_set(v___x_5549_, 1, v___x_5548_);
v___x_5550_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5551_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5552_, 0, v_a_5546_);
lean_ctor_set(v___x_5552_, 1, v___x_5550_);
lean_ctor_set(v___x_5552_, 2, v___x_5551_);
v___x_5553_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5552_, 3);
v___x_5554_ = l_Lean_Syntax_node2(v_a_5546_, v___x_5553_, v___x_5552_, v___y_5496_);
v___x_5555_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5550_, v___x_5554_);
v___x_5556_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5557_, 0, v_a_5546_);
lean_ctor_set(v___x_5557_, 1, v___x_5556_);
v___x_5558_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5559_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5560_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5561_, 0, v_a_5546_);
lean_ctor_set(v___x_5561_, 1, v___x_5560_);
v___x_5562_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5550_, v___y_5494_);
v___x_5563_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5550_, v___x_5562_);
v___x_5564_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5565_, 0, v_a_5546_);
lean_ctor_set(v___x_5565_, 1, v___x_5564_);
lean_inc_ref(v___x_5565_);
lean_inc_ref(v___x_5561_);
v___x_5566_ = l_Lean_Syntax_node4(v_a_5546_, v___x_5559_, v___x_5561_, v___x_5563_, v___x_5565_, v_body_5498_);
v___x_5567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5568_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5569_, 0, v_a_5546_);
lean_ctor_set(v___x_5569_, 1, v___x_5568_);
v___x_5570_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5567_, v___x_5569_);
v___x_5571_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5550_, v___x_5570_);
v___x_5572_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5550_, v___x_5571_);
v___x_5573_ = l_Lean_Syntax_node4(v_a_5546_, v___x_5559_, v___x_5561_, v___x_5572_, v___x_5565_, v___y_5493_);
v___x_5574_ = l_Lean_Syntax_node2(v_a_5546_, v___x_5550_, v___x_5566_, v___x_5573_);
v___x_5575_ = l_Lean_Syntax_node1(v_a_5546_, v___x_5558_, v___x_5574_);
v___x_5576_ = l_Lean_Syntax_node7(v_a_5546_, v___x_5547_, v___x_5549_, v___x_5552_, v___x_5552_, v___x_5552_, v___x_5555_, v___x_5557_, v___x_5575_);
v___x_5577_ = l_Lean_Elab_Do_elabDoElem(v___x_5576_, v_dec_5480_, v___x_5490_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
return v___x_5577_;
}
}
v___jp_5578_:
{
if (lean_obj_tag(v___y_5582_) == 0)
{
lean_dec_ref(v___y_5580_);
v___y_5493_ = v___y_5589_;
v___y_5494_ = v___y_5590_;
v___y_5495_ = v___y_5583_;
v___y_5496_ = v___y_5585_;
v___y_5497_ = v___y_5593_;
v_body_5498_ = v_a_5594_;
v___y_5499_ = v___y_5587_;
v___y_5500_ = v___y_5588_;
v___y_5501_ = v___y_5591_;
v___y_5502_ = v___y_5592_;
v___y_5503_ = v___y_5579_;
v___y_5504_ = v___y_5584_;
v___y_5505_ = v___y_5581_;
goto v___jp_5492_;
}
else
{
lean_dec_ref(v___y_5582_);
if (v___y_5586_ == 0)
{
lean_dec_ref(v___y_5580_);
v___y_5493_ = v___y_5589_;
v___y_5494_ = v___y_5590_;
v___y_5495_ = v___y_5583_;
v___y_5496_ = v___y_5585_;
v___y_5497_ = v___y_5593_;
v_body_5498_ = v_a_5594_;
v___y_5499_ = v___y_5587_;
v___y_5500_ = v___y_5588_;
v___y_5501_ = v___y_5591_;
v___y_5502_ = v___y_5592_;
v___y_5503_ = v___y_5579_;
v___y_5504_ = v___y_5584_;
v___y_5505_ = v___y_5581_;
goto v___jp_5492_;
}
else
{
size_t v_sz_5595_; size_t v___x_5596_; lean_object* v___x_5597_; 
v_sz_5595_ = lean_array_size(v___y_5580_);
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5580_, v_sz_5595_, v___x_5596_, v_a_5594_, v___y_5587_, v___y_5588_, v___y_5591_, v___y_5592_, v___y_5579_, v___y_5584_, v___y_5581_);
lean_dec_ref(v___y_5580_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc(v_a_5598_);
lean_dec_ref(v___x_5597_);
v___y_5493_ = v___y_5589_;
v___y_5494_ = v___y_5590_;
v___y_5495_ = v___y_5583_;
v___y_5496_ = v___y_5585_;
v___y_5497_ = v___y_5593_;
v_body_5498_ = v_a_5598_;
v___y_5499_ = v___y_5587_;
v___y_5500_ = v___y_5588_;
v___y_5501_ = v___y_5591_;
v___y_5502_ = v___y_5592_;
v___y_5503_ = v___y_5579_;
v___y_5504_ = v___y_5584_;
v___y_5505_ = v___y_5581_;
goto v___jp_5492_;
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
lean_dec(v___y_5590_);
lean_dec(v___y_5589_);
lean_dec(v___y_5585_);
lean_dec_ref(v___y_5583_);
lean_dec_ref(v_dec_5480_);
v_a_5599_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5597_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5597_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
}
}
v___jp_5607_:
{
uint8_t v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v___x_5622_ = 0;
v___x_5623_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5624_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5614_, v___y_5610_, v___x_5623_, v___y_5616_, v___y_5619_, v___y_5620_, v___y_5608_, v___y_5611_, v___y_5609_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_object* v_a_5625_; lean_object* v___x_5626_; 
v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
lean_inc(v_a_5625_);
lean_dec_ref(v___x_5624_);
v___x_5626_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5625_, v___y_5615_, v___y_5616_, v___y_5619_, v___y_5620_, v___y_5608_, v___y_5611_, v___y_5609_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_object* v___x_5627_; 
lean_dec_ref(v___x_5626_);
lean_inc(v___y_5618_);
v___x_5627_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5618_, v___y_5616_, v___y_5619_, v___y_5620_, v___y_5608_, v___y_5611_, v___y_5609_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5628_);
lean_dec_ref(v___x_5627_);
lean_inc(v___y_5610_);
v___x_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5629_, 0, v___y_5610_);
v___x_5630_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5629_, v_a_5628_, v___y_5615_, v___y_5616_, v___y_5619_, v___y_5620_, v___y_5608_, v___y_5611_, v___y_5609_);
lean_dec_ref(v___x_5629_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_dec_ref(v___x_5630_);
if (lean_obj_tag(v___y_5621_) == 0)
{
lean_object* v_ref_5631_; lean_object* v_quotContext_5632_; lean_object* v_currMacroScope_5633_; lean_object* v___x_5634_; lean_object* v_a_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v_ref_5631_ = lean_ctor_get(v___y_5611_, 5);
v_quotContext_5632_ = lean_ctor_get(v___y_5611_, 10);
v_currMacroScope_5633_ = lean_ctor_get(v___y_5611_, 11);
v___x_5634_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5631_, v___y_5615_, v___y_5616_, v___y_5619_, v___y_5620_, v___y_5608_, v___y_5611_, v___y_5609_);
v_a_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc_n(v_a_5635_, 9);
lean_dec_ref(v___x_5634_);
v___x_5636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5637_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5639_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5640_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5641_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5633_, 2);
lean_inc_n(v_quotContext_5632_, 2);
v___x_5643_ = l_Lean_addMacroScope(v_quotContext_5632_, v___x_5642_, v_currMacroScope_5633_);
v___x_5644_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5645_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5645_, 0, v_a_5635_);
lean_ctor_set(v___x_5645_, 1, v___x_5641_);
lean_ctor_set(v___x_5645_, 2, v___x_5643_);
lean_ctor_set(v___x_5645_, 3, v___x_5644_);
v___x_5646_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5647_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5648_ = l_Lean_addMacroScope(v_quotContext_5632_, v___x_5647_, v_currMacroScope_5633_);
v___x_5649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5650_, 0, v_a_5635_);
lean_ctor_set(v___x_5650_, 1, v___x_5646_);
lean_ctor_set(v___x_5650_, 2, v___x_5648_);
lean_ctor_set(v___x_5650_, 3, v___x_5649_);
v___x_5651_ = l_Lean_Syntax_node1(v_a_5635_, v___x_5637_, v___x_5650_);
v___x_5652_ = l_Lean_Syntax_node2(v_a_5635_, v___x_5640_, v___x_5645_, v___x_5651_);
v___x_5653_ = l_Lean_Syntax_node1(v_a_5635_, v___x_5639_, v___x_5652_);
v___x_5654_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5655_, 0, v_a_5635_);
lean_ctor_set(v___x_5655_, 1, v___x_5637_);
lean_ctor_set(v___x_5655_, 2, v___x_5654_);
v___x_5656_ = l_Lean_Syntax_node2(v_a_5635_, v___x_5638_, v___x_5653_, v___x_5655_);
v___x_5657_ = l_Lean_Syntax_node1(v_a_5635_, v___x_5637_, v___x_5656_);
v___x_5658_ = l_Lean_Syntax_node1(v_a_5635_, v___x_5636_, v___x_5657_);
v___y_5579_ = v___y_5608_;
v___y_5580_ = v_a_5628_;
v___y_5581_ = v___y_5609_;
v___y_5582_ = v___y_5610_;
v___y_5583_ = v_a_5625_;
v___y_5584_ = v___y_5611_;
v___y_5585_ = v___y_5612_;
v___y_5586_ = v___y_5613_;
v___y_5587_ = v___y_5615_;
v___y_5588_ = v___y_5616_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5618_;
v___y_5591_ = v___y_5619_;
v___y_5592_ = v___y_5620_;
v___y_5593_ = v___x_5622_;
v_a_5594_ = v___x_5658_;
goto v___jp_5578_;
}
else
{
lean_object* v_val_5659_; 
v_val_5659_ = lean_ctor_get(v___y_5621_, 0);
lean_inc(v_val_5659_);
lean_dec_ref(v___y_5621_);
v___y_5579_ = v___y_5608_;
v___y_5580_ = v_a_5628_;
v___y_5581_ = v___y_5609_;
v___y_5582_ = v___y_5610_;
v___y_5583_ = v_a_5625_;
v___y_5584_ = v___y_5611_;
v___y_5585_ = v___y_5612_;
v___y_5586_ = v___y_5613_;
v___y_5587_ = v___y_5615_;
v___y_5588_ = v___y_5616_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5618_;
v___y_5591_ = v___y_5619_;
v___y_5592_ = v___y_5620_;
v___y_5593_ = v___x_5622_;
v_a_5594_ = v_val_5659_;
goto v___jp_5578_;
}
}
else
{
lean_object* v_a_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5667_; 
lean_dec(v_a_5628_);
lean_dec(v_a_5625_);
lean_dec(v___y_5621_);
lean_dec(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec(v___y_5612_);
lean_dec(v___y_5610_);
lean_dec_ref(v_dec_5480_);
v_a_5660_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5662_ = v___x_5630_;
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_a_5660_);
lean_dec(v___x_5630_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5667_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v___x_5665_; 
if (v_isShared_5663_ == 0)
{
v___x_5665_ = v___x_5662_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5660_);
v___x_5665_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
return v___x_5665_;
}
}
}
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5675_; 
lean_dec(v_a_5625_);
lean_dec(v___y_5621_);
lean_dec(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec(v___y_5612_);
lean_dec(v___y_5610_);
lean_dec_ref(v_dec_5480_);
v_a_5668_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5670_ = v___x_5627_;
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_a_5668_);
lean_dec(v___x_5627_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
}
else
{
lean_object* v_a_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5683_; 
lean_dec(v_a_5625_);
lean_dec(v___y_5621_);
lean_dec(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec(v___y_5612_);
lean_dec(v___y_5610_);
lean_dec_ref(v_dec_5480_);
v_a_5676_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5683_ == 0)
{
v___x_5678_ = v___x_5626_;
v_isShared_5679_ = v_isSharedCheck_5683_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_a_5676_);
lean_dec(v___x_5626_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5683_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
lean_object* v___x_5681_; 
if (v_isShared_5679_ == 0)
{
v___x_5681_ = v___x_5678_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
v___x_5681_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
return v___x_5681_;
}
}
}
}
else
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5691_; 
lean_dec(v___y_5621_);
lean_dec(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec(v___y_5612_);
lean_dec(v___y_5610_);
lean_dec_ref(v_dec_5480_);
v_a_5684_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5691_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5691_ == 0)
{
v___x_5686_ = v___x_5624_;
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5624_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5691_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5689_; 
if (v_isShared_5687_ == 0)
{
v___x_5689_ = v___x_5686_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
}
v___jp_5692_:
{
lean_object* v___x_5701_; lean_object* v_cfg_5702_; lean_object* v___x_5703_; uint8_t v___x_5704_; 
v___x_5701_ = lean_unsigned_to_nat(2u);
v_cfg_5702_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5701_);
v___x_5703_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5702_);
v___x_5704_ = l_Lean_Syntax_isOfKind(v_cfg_5702_, v___x_5703_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5705_; 
lean_dec(v_cfg_5702_);
lean_dec(v_mutTk_x3f_5693_);
lean_dec_ref(v_dec_5480_);
lean_dec(v_stx_5479_);
v___x_5705_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5705_;
}
else
{
lean_object* v___x_5706_; lean_object* v_pattern_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
v___x_5706_ = lean_unsigned_to_nat(3u);
v_pattern_5707_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5706_);
v___x_5708_ = lean_unsigned_to_nat(5u);
v___x_5709_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5708_);
v___x_5710_ = lean_unsigned_to_nat(7u);
v___x_5711_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5710_);
v___x_5712_ = lean_unsigned_to_nat(8u);
v___x_5713_ = l_Lean_Syntax_getArg(v_stx_5479_, v___x_5712_);
lean_dec(v_stx_5479_);
v___x_5714_ = l_Lean_Syntax_getOptional_x3f(v___x_5713_);
lean_dec(v___x_5713_);
if (lean_obj_tag(v___x_5714_) == 0)
{
lean_object* v___x_5715_; 
v___x_5715_ = lean_box(0);
v___y_5608_ = v___y_5698_;
v___y_5609_ = v___y_5700_;
v___y_5610_ = v_mutTk_x3f_5693_;
v___y_5611_ = v___y_5699_;
v___y_5612_ = v___x_5709_;
v___y_5613_ = v___x_5704_;
v___y_5614_ = v_cfg_5702_;
v___y_5615_ = v___y_5694_;
v___y_5616_ = v___y_5695_;
v___y_5617_ = v___x_5711_;
v___y_5618_ = v_pattern_5707_;
v___y_5619_ = v___y_5696_;
v___y_5620_ = v___y_5697_;
v___y_5621_ = v___x_5715_;
goto v___jp_5607_;
}
else
{
lean_object* v_val_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5723_; 
v_val_5716_ = lean_ctor_get(v___x_5714_, 0);
v_isSharedCheck_5723_ = !lean_is_exclusive(v___x_5714_);
if (v_isSharedCheck_5723_ == 0)
{
v___x_5718_ = v___x_5714_;
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
else
{
lean_inc(v_val_5716_);
lean_dec(v___x_5714_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5721_; 
if (v_isShared_5719_ == 0)
{
v___x_5721_ = v___x_5718_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_val_5716_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
v___y_5608_ = v___y_5698_;
v___y_5609_ = v___y_5700_;
v___y_5610_ = v_mutTk_x3f_5693_;
v___y_5611_ = v___y_5699_;
v___y_5612_ = v___x_5709_;
v___y_5613_ = v___x_5704_;
v___y_5614_ = v_cfg_5702_;
v___y_5615_ = v___y_5694_;
v___y_5616_ = v___y_5695_;
v___y_5617_ = v___x_5711_;
v___y_5618_ = v_pattern_5707_;
v___y_5619_ = v___y_5696_;
v___y_5620_ = v___y_5697_;
v___y_5621_ = v___x_5721_;
goto v___jp_5607_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5733_, lean_object* v_dec_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_){
_start:
{
lean_object* v_res_5743_; 
v_res_5743_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5733_, v_dec_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
lean_dec(v_a_5739_);
lean_dec_ref(v_a_5738_);
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec_ref(v_a_5735_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5744_, size_t v_sz_5745_, size_t v_i_5746_, lean_object* v_b_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5744_, v_sz_5745_, v_i_5746_, v_b_5747_, v___y_5753_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5757_, lean_object* v_sz_5758_, lean_object* v_i_5759_, lean_object* v_b_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
size_t v_sz_boxed_5769_; size_t v_i_boxed_5770_; lean_object* v_res_5771_; 
v_sz_boxed_5769_ = lean_unbox_usize(v_sz_5758_);
lean_dec(v_sz_5758_);
v_i_boxed_5770_ = lean_unbox_usize(v_i_5759_);
lean_dec(v_i_5759_);
v_res_5771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5757_, v_sz_boxed_5769_, v_i_boxed_5770_, v_b_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec_ref(v_as_5757_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5779_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5780_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5782_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5783_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5779_, v___x_5780_, v___x_5781_, v___x_5782_);
return v___x_5783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5785_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5793_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5794_ = l_Lean_stringToMessageData(v___x_5793_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5795_, lean_object* v_dec_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_){
_start:
{
lean_object* v___x_5805_; uint8_t v___x_5806_; 
v___x_5805_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5795_);
v___x_5806_ = l_Lean_Syntax_isOfKind(v_stx_5795_, v___x_5805_);
if (v___x_5806_ == 0)
{
lean_object* v___x_5807_; 
lean_dec_ref(v_dec_5796_);
lean_dec(v_stx_5795_);
v___x_5807_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5807_;
}
else
{
lean_object* v___x_5808_; lean_object* v_tk_5809_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5844_; lean_object* v___y_5845_; uint8_t v___y_5846_; lean_object* v___y_5847_; lean_object* v___y_5848_; lean_object* v___y_5849_; lean_object* v___y_5850_; lean_object* v___y_5851_; lean_object* v___y_5852_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; uint8_t v___y_5856_; lean_object* v___y_5859_; lean_object* v___y_5860_; uint8_t v___y_5861_; lean_object* v___y_5862_; lean_object* v___y_5863_; lean_object* v___y_5864_; lean_object* v___y_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; uint8_t v___y_5871_; lean_object* v_mutTk_x3f_5874_; lean_object* v___y_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___y_5880_; lean_object* v___y_5881_; lean_object* v___x_5911_; lean_object* v___x_5912_; uint8_t v___x_5913_; 
v___x_5808_ = lean_unsigned_to_nat(0u);
v_tk_5809_ = l_Lean_Syntax_getArg(v_stx_5795_, v___x_5808_);
v___x_5911_ = lean_unsigned_to_nat(1u);
v___x_5912_ = l_Lean_Syntax_getArg(v_stx_5795_, v___x_5911_);
v___x_5913_ = l_Lean_Syntax_isNone(v___x_5912_);
if (v___x_5913_ == 0)
{
uint8_t v___x_5914_; 
lean_inc(v___x_5912_);
v___x_5914_ = l_Lean_Syntax_matchesNull(v___x_5912_, v___x_5911_);
if (v___x_5914_ == 0)
{
lean_object* v___x_5915_; 
lean_dec(v___x_5912_);
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
lean_dec(v_stx_5795_);
v___x_5915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5915_;
}
else
{
lean_object* v_mutTk_x3f_5916_; lean_object* v___x_5917_; 
v_mutTk_x3f_5916_ = l_Lean_Syntax_getArg(v___x_5912_, v___x_5808_);
lean_dec(v___x_5912_);
v___x_5917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5917_, 0, v_mutTk_x3f_5916_);
v_mutTk_x3f_5874_ = v___x_5917_;
v___y_5875_ = v_a_5797_;
v___y_5876_ = v_a_5798_;
v___y_5877_ = v_a_5799_;
v___y_5878_ = v_a_5800_;
v___y_5879_ = v_a_5801_;
v___y_5880_ = v_a_5802_;
v___y_5881_ = v_a_5803_;
goto v___jp_5873_;
}
}
else
{
lean_object* v___x_5918_; 
lean_dec(v___x_5912_);
v___x_5918_ = lean_box(0);
v_mutTk_x3f_5874_ = v___x_5918_;
v___y_5875_ = v_a_5797_;
v___y_5876_ = v_a_5798_;
v___y_5877_ = v_a_5799_;
v___y_5878_ = v_a_5800_;
v___y_5879_ = v_a_5801_;
v___y_5880_ = v_a_5802_;
v___y_5881_ = v_a_5803_;
goto v___jp_5873_;
}
v___jp_5810_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5820_, 0, v___y_5811_);
v___x_5821_ = l_Lean_Elab_Do_elabDoArrow(v___x_5820_, v___y_5812_, v_tk_5809_, v_dec_5796_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_);
lean_dec(v_tk_5809_);
return v___x_5821_;
}
v___jp_5822_:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5842_; 
lean_dec(v___y_5829_);
lean_dec(v___y_5824_);
v___x_5833_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5834_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5830_, v___x_5833_, v___y_5828_, v___y_5831_, v___y_5827_, v___y_5826_);
lean_dec(v___y_5830_);
v_a_5835_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5837_ = v___x_5834_;
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5834_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5838_ == 0)
{
v___x_5840_ = v___x_5837_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
v___jp_5843_:
{
if (v___y_5856_ == 0)
{
lean_object* v_eq_x3f_5857_; 
v_eq_x3f_5857_ = lean_ctor_get(v___y_5855_, 0);
lean_inc(v_eq_x3f_5857_);
lean_dec_ref(v___y_5855_);
if (lean_obj_tag(v_eq_x3f_5857_) == 0)
{
lean_dec(v___y_5853_);
v___y_5811_ = v___y_5844_;
v___y_5812_ = v___y_5852_;
v___y_5813_ = v___y_5849_;
v___y_5814_ = v___y_5848_;
v___y_5815_ = v___y_5847_;
v___y_5816_ = v___y_5845_;
v___y_5817_ = v___y_5854_;
v___y_5818_ = v___y_5850_;
v___y_5819_ = v___y_5851_;
goto v___jp_5810_;
}
else
{
lean_dec_ref(v_eq_x3f_5857_);
if (v___y_5846_ == 0)
{
lean_dec(v___y_5853_);
v___y_5811_ = v___y_5844_;
v___y_5812_ = v___y_5852_;
v___y_5813_ = v___y_5849_;
v___y_5814_ = v___y_5848_;
v___y_5815_ = v___y_5847_;
v___y_5816_ = v___y_5845_;
v___y_5817_ = v___y_5854_;
v___y_5818_ = v___y_5850_;
v___y_5819_ = v___y_5851_;
goto v___jp_5810_;
}
else
{
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
v___y_5823_ = v___y_5848_;
v___y_5824_ = v___y_5844_;
v___y_5825_ = v___y_5849_;
v___y_5826_ = v___y_5851_;
v___y_5827_ = v___y_5850_;
v___y_5828_ = v___y_5845_;
v___y_5829_ = v___y_5852_;
v___y_5830_ = v___y_5853_;
v___y_5831_ = v___y_5854_;
v___y_5832_ = v___y_5847_;
goto v___jp_5822_;
}
}
}
else
{
lean_dec_ref(v___y_5855_);
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
v___y_5823_ = v___y_5848_;
v___y_5824_ = v___y_5844_;
v___y_5825_ = v___y_5849_;
v___y_5826_ = v___y_5851_;
v___y_5827_ = v___y_5850_;
v___y_5828_ = v___y_5845_;
v___y_5829_ = v___y_5852_;
v___y_5830_ = v___y_5853_;
v___y_5831_ = v___y_5854_;
v___y_5832_ = v___y_5847_;
goto v___jp_5822_;
}
}
v___jp_5858_:
{
if (v___y_5871_ == 0)
{
uint8_t v_zeta_5872_; 
v_zeta_5872_ = lean_ctor_get_uint8(v___y_5870_, sizeof(void*)*1 + 2);
v___y_5844_ = v___y_5859_;
v___y_5845_ = v___y_5860_;
v___y_5846_ = v___y_5861_;
v___y_5847_ = v___y_5862_;
v___y_5848_ = v___y_5863_;
v___y_5849_ = v___y_5864_;
v___y_5850_ = v___y_5865_;
v___y_5851_ = v___y_5866_;
v___y_5852_ = v___y_5867_;
v___y_5853_ = v___y_5868_;
v___y_5854_ = v___y_5869_;
v___y_5855_ = v___y_5870_;
v___y_5856_ = v_zeta_5872_;
goto v___jp_5843_;
}
else
{
v___y_5844_ = v___y_5859_;
v___y_5845_ = v___y_5860_;
v___y_5846_ = v___y_5861_;
v___y_5847_ = v___y_5862_;
v___y_5848_ = v___y_5863_;
v___y_5849_ = v___y_5864_;
v___y_5850_ = v___y_5865_;
v___y_5851_ = v___y_5866_;
v___y_5852_ = v___y_5867_;
v___y_5853_ = v___y_5868_;
v___y_5854_ = v___y_5869_;
v___y_5855_ = v___y_5870_;
v___y_5856_ = v___x_5806_;
goto v___jp_5843_;
}
}
v___jp_5873_:
{
lean_object* v___x_5882_; lean_object* v_cfg_5883_; lean_object* v___x_5884_; uint8_t v___x_5885_; 
v___x_5882_ = lean_unsigned_to_nat(2u);
v_cfg_5883_ = l_Lean_Syntax_getArg(v_stx_5795_, v___x_5882_);
v___x_5884_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5883_);
v___x_5885_ = l_Lean_Syntax_isOfKind(v_cfg_5883_, v___x_5884_);
if (v___x_5885_ == 0)
{
lean_object* v___x_5886_; 
lean_dec(v_cfg_5883_);
lean_dec(v_mutTk_x3f_5874_);
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
lean_dec(v_stx_5795_);
v___x_5886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5886_;
}
else
{
lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5887_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5883_);
v___x_5888_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5883_, v_mutTk_x3f_5874_, v___x_5887_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5890_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_a_5889_);
lean_dec_ref(v___x_5888_);
v___x_5890_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5889_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
if (lean_obj_tag(v___x_5890_) == 0)
{
uint8_t v_nondep_5891_; uint8_t v_usedOnly_5892_; lean_object* v___x_5893_; lean_object* v_decl_5894_; 
lean_dec_ref(v___x_5890_);
v_nondep_5891_ = lean_ctor_get_uint8(v_a_5889_, sizeof(void*)*1);
v_usedOnly_5892_ = lean_ctor_get_uint8(v_a_5889_, sizeof(void*)*1 + 1);
v___x_5893_ = lean_unsigned_to_nat(3u);
v_decl_5894_ = l_Lean_Syntax_getArg(v_stx_5795_, v___x_5893_);
lean_dec(v_stx_5795_);
if (v_nondep_5891_ == 0)
{
v___y_5859_ = v_mutTk_x3f_5874_;
v___y_5860_ = v___y_5878_;
v___y_5861_ = v___x_5885_;
v___y_5862_ = v___y_5877_;
v___y_5863_ = v___y_5876_;
v___y_5864_ = v___y_5875_;
v___y_5865_ = v___y_5880_;
v___y_5866_ = v___y_5881_;
v___y_5867_ = v_decl_5894_;
v___y_5868_ = v_cfg_5883_;
v___y_5869_ = v___y_5879_;
v___y_5870_ = v_a_5889_;
v___y_5871_ = v_usedOnly_5892_;
goto v___jp_5858_;
}
else
{
v___y_5859_ = v_mutTk_x3f_5874_;
v___y_5860_ = v___y_5878_;
v___y_5861_ = v___x_5885_;
v___y_5862_ = v___y_5877_;
v___y_5863_ = v___y_5876_;
v___y_5864_ = v___y_5875_;
v___y_5865_ = v___y_5880_;
v___y_5866_ = v___y_5881_;
v___y_5867_ = v_decl_5894_;
v___y_5868_ = v_cfg_5883_;
v___y_5869_ = v___y_5879_;
v___y_5870_ = v_a_5889_;
v___y_5871_ = v___x_5806_;
goto v___jp_5858_;
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec(v_a_5889_);
lean_dec(v_cfg_5883_);
lean_dec(v_mutTk_x3f_5874_);
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
lean_dec(v_stx_5795_);
v_a_5895_ = lean_ctor_get(v___x_5890_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5890_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5890_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5890_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5910_; 
lean_dec(v_cfg_5883_);
lean_dec(v_mutTk_x3f_5874_);
lean_dec(v_tk_5809_);
lean_dec_ref(v_dec_5796_);
lean_dec(v_stx_5795_);
v_a_5903_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5905_ = v___x_5888_;
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
else
{
lean_inc(v_a_5903_);
lean_dec(v___x_5888_);
v___x_5905_ = lean_box(0);
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
v_resetjp_5904_:
{
lean_object* v___x_5908_; 
if (v_isShared_5906_ == 0)
{
v___x_5908_ = v___x_5905_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5919_, lean_object* v_dec_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_){
_start:
{
lean_object* v_res_5929_; 
v_res_5929_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5919_, v_dec_5920_, v_a_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_);
lean_dec(v_a_5927_);
lean_dec_ref(v_a_5926_);
lean_dec(v_a_5925_);
lean_dec_ref(v_a_5924_);
lean_dec(v_a_5923_);
lean_dec_ref(v_a_5922_);
lean_dec_ref(v_a_5921_);
return v_res_5929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5937_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5938_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5939_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5940_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5937_, v___x_5938_, v___x_5939_, v___x_5940_);
return v___x_5941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5942_){
_start:
{
lean_object* v_res_5943_; 
v_res_5943_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5950_, lean_object* v_dec_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_){
_start:
{
lean_object* v___x_5960_; uint8_t v___x_5961_; 
v___x_5960_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5950_);
v___x_5961_ = l_Lean_Syntax_isOfKind(v_stx_5950_, v___x_5960_);
if (v___x_5961_ == 0)
{
lean_object* v___x_5962_; 
lean_dec_ref(v_dec_5951_);
lean_dec(v_stx_5950_);
v___x_5962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5962_;
}
else
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; uint8_t v___x_5966_; 
v___x_5963_ = lean_unsigned_to_nat(0u);
v___x_5964_ = l_Lean_Syntax_getArg(v_stx_5950_, v___x_5963_);
lean_dec(v_stx_5950_);
v___x_5965_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5964_);
v___x_5966_ = l_Lean_Syntax_isOfKind(v___x_5964_, v___x_5965_);
if (v___x_5966_ == 0)
{
lean_object* v___x_5967_; uint8_t v___x_5968_; 
v___x_5967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5964_);
v___x_5968_ = l_Lean_Syntax_isOfKind(v___x_5964_, v___x_5967_);
if (v___x_5968_ == 0)
{
lean_object* v___x_5969_; 
lean_dec(v___x_5964_);
lean_dec_ref(v_dec_5951_);
v___x_5969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5969_;
}
else
{
lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5970_ = lean_box(2);
lean_inc(v___x_5964_);
v___x_5971_ = l_Lean_Elab_Do_elabDoArrow(v___x_5970_, v___x_5964_, v___x_5964_, v_dec_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
lean_dec(v___x_5964_);
return v___x_5971_;
}
}
else
{
lean_object* v___x_5972_; lean_object* v___x_5973_; 
v___x_5972_ = lean_box(2);
lean_inc(v___x_5964_);
v___x_5973_ = l_Lean_Elab_Do_elabDoArrow(v___x_5972_, v___x_5964_, v___x_5964_, v_dec_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
lean_dec(v___x_5964_);
return v___x_5973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5974_, lean_object* v_dec_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_){
_start:
{
lean_object* v_res_5984_; 
v_res_5984_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5974_, v_dec_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_);
lean_dec(v_a_5982_);
lean_dec_ref(v_a_5981_);
lean_dec(v_a_5980_);
lean_dec_ref(v_a_5979_);
lean_dec(v_a_5978_);
lean_dec_ref(v_a_5977_);
lean_dec_ref(v_a_5976_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5992_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5995_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5996_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5992_, v___x_5993_, v___x_5994_, v___x_5995_);
return v___x_5996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5998_;
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
