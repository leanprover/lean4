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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Do_registerMutVarAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0;
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
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_7_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_as_75_, size_t v_sz_76_, size_t v_i_77_, lean_object* v_b_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = lean_usize_dec_lt(v_i_77_, v_sz_76_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v_b_78_);
return v___x_88_;
}
else
{
lean_object* v_a_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_a_89_ = lean_array_uget_borrowed(v_as_75_, v_i_77_);
v___x_90_ = l_Lean_TSyntax_getId(v_a_89_);
v___x_91_ = l_Lean_Elab_Do_registerMutVarAlias(v___x_90_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___x_92_; size_t v___x_93_; size_t v___x_94_; 
lean_dec_ref_known(v___x_91_, 1);
v___x_92_ = lean_box(0);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_i_77_, v___x_93_);
v_i_77_ = v___x_94_;
v_b_78_ = v___x_92_;
goto _start;
}
else
{
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_as_96_, lean_object* v_sz_97_, lean_object* v_i_98_, lean_object* v_b_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
size_t v_sz_boxed_108_; size_t v_i_boxed_109_; lean_object* v_res_110_; 
v_sz_boxed_108_ = lean_unbox_usize(v_sz_97_);
lean_dec(v_sz_97_);
v_i_boxed_109_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_as_96_, v_sz_boxed_108_, v_i_boxed_109_, v_b_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v_as_96_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_111_, lean_object* v_vars_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
if (lean_obj_tag(v_letOrReassign_111_) == 2)
{
lean_object* v___x_121_; size_t v_sz_122_; size_t v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_box(0);
v_sz_122_ = lean_array_size(v_vars_112_);
v___x_123_ = ((size_t)0ULL);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_vars_112_, v_sz_122_, v___x_123_, v___x_121_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_132_);
v___x_126_ = v___x_124_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_121_);
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_121_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
return v___x_124_;
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_135_, lean_object* v_vars_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_135_, v_vars_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec_ref(v_vars_136_);
lean_dec(v_letOrReassign_135_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(lean_object* v_elabBody_146_, lean_object* v_body_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; 
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
v___x_156_ = lean_apply_8(v_elabBody_146_, v_body_147_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object* v_elabBody_157_, lean_object* v_body_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(v_elabBody_157_, v_body_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(lean_object* v_letOrReassign_168_, lean_object* v_vars_169_, lean_object* v_k_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_168_, v_vars_169_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; 
lean_dec_ref_known(v___x_179_, 1);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc_ref(v___y_171_);
v___x_180_ = lean_apply_8(v_k_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, lean_box(0));
return v___x_180_;
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v_k_170_);
v_a_181_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed(lean_object* v_letOrReassign_189_, lean_object* v_vars_190_, lean_object* v_k_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(v_letOrReassign_189_, v_vars_190_, v_k_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_vars_190_);
lean_dec(v_letOrReassign_189_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith(lean_object* v_hint_201_, lean_object* v_letOrReassign_202_, lean_object* v_vars_203_, lean_object* v_k_204_, lean_object* v_elabBody_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v_elabCont_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___f_214_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed), 10, 1);
lean_closure_set(v___f_214_, 0, v_elabBody_205_);
lean_inc_ref(v_vars_203_);
lean_inc(v_letOrReassign_202_);
v___f_215_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_215_, 0, v_letOrReassign_202_);
lean_closure_set(v___f_215_, 1, v_vars_203_);
lean_closure_set(v___f_215_, 2, v_k_204_);
v___x_216_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_202_);
lean_dec(v_letOrReassign_202_);
v_elabCont_217_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVars_x3f___boxed), 12, 4);
lean_closure_set(v_elabCont_217_, 0, lean_box(0));
lean_closure_set(v_elabCont_217_, 1, v___x_216_);
lean_closure_set(v_elabCont_217_, 2, v_vars_203_);
lean_closure_set(v_elabCont_217_, 3, v___f_215_);
v___x_218_ = lean_box(0);
v___x_219_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v_hint_201_, v_elabCont_217_, v___f_214_, v___x_218_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___boxed(lean_object* v_hint_220_, lean_object* v_letOrReassign_221_, lean_object* v_vars_222_, lean_object* v_k_223_, lean_object* v_elabBody_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Elab_Do_elabDoLetOrReassignWith(v_hint_220_, v_letOrReassign_221_, v_vars_222_, v_k_223_, v_elabBody_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_234_, lean_object* v_vars_235_, lean_object* v_k_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc_ref(v_vars_235_);
lean_inc(v_letOrReassign_234_);
v___f_245_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_245_, 0, v_letOrReassign_234_);
lean_closure_set(v___f_245_, 1, v_vars_235_);
lean_closure_set(v___f_245_, 2, v_k_236_);
v___x_246_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_234_);
lean_dec(v_letOrReassign_234_);
v___x_247_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_246_, v_vars_235_, v___f_245_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_248_, lean_object* v_vars_249_, lean_object* v_k_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_248_, v_vars_249_, v_k_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_278_, lean_object* v_a_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_288_, lean_object* v_a_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_288_, v_a_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v_env_305_; lean_object* v___x_306_; lean_object* v_mctx_307_; lean_object* v_lctx_308_; lean_object* v_options_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_304_ = lean_st_ref_get(v___y_302_);
v_env_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_env_305_);
lean_dec(v___x_304_);
v___x_306_ = lean_st_ref_get(v___y_300_);
v_mctx_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_mctx_307_);
lean_dec(v___x_306_);
v_lctx_308_ = lean_ctor_get(v___y_299_, 2);
v_options_309_ = lean_ctor_get(v___y_301_, 2);
lean_inc_ref(v_options_309_);
lean_inc_ref(v_lctx_308_);
v___x_310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_310_, 0, v_env_305_);
lean_ctor_set(v___x_310_, 1, v_mctx_307_);
lean_ctor_set(v___x_310_, 2, v_lctx_308_);
lean_ctor_set(v___x_310_, 3, v_options_309_);
v___x_311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_msgData_298_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_box(1);
v___x_321_ = l_Lean_MessageData_ofFormat(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2));
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
return v_x_327_;
}
else
{
lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_352_; 
v_head_329_ = lean_ctor_get(v_x_328_, 0);
v_tail_330_ = lean_ctor_get(v_x_328_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_352_ == 0)
{
v___x_332_ = v_x_328_;
v_isShared_333_ = v_isSharedCheck_352_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_head_329_);
lean_dec(v_x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_352_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_before_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_350_; 
v_before_334_ = lean_ctor_get(v_head_329_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_head_329_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_head_329_, 1);
lean_dec(v_unused_351_);
v___x_336_ = v_head_329_;
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_before_334_);
lean_dec(v_head_329_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 7);
lean_ctor_set(v___x_336_, 1, v___x_338_);
lean_ctor_set(v___x_336_, 0, v_x_327_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_x_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_349_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 7);
lean_ctor_set(v___x_332_, 1, v___x_341_);
lean_ctor_set(v___x_332_, 0, v___x_340_);
v___x_343_ = v___x_332_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_MessageData_ofSyntax(v_before_334_);
v___x_345_ = l_Lean_indentD(v___x_344_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v_x_327_ = v___x_346_;
v_x_328_ = v_tail_330_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object* v_opts_353_, lean_object* v_opt_354_){
_start:
{
lean_object* v_name_355_; lean_object* v_defValue_356_; lean_object* v_map_357_; lean_object* v___x_358_; 
v_name_355_ = lean_ctor_get(v_opt_354_, 0);
v_defValue_356_ = lean_ctor_get(v_opt_354_, 1);
v_map_357_ = lean_ctor_get(v_opts_353_, 0);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_357_, v_name_355_);
if (lean_obj_tag(v___x_358_) == 0)
{
uint8_t v___x_359_; 
v___x_359_ = lean_unbox(v_defValue_356_);
return v___x_359_;
}
else
{
lean_object* v_val_360_; 
v_val_360_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v___x_358_, 1);
if (lean_obj_tag(v_val_360_) == 1)
{
uint8_t v_v_361_; 
v_v_361_ = lean_ctor_get_uint8(v_val_360_, 0);
lean_dec_ref_known(v_val_360_, 0);
return v_v_361_;
}
else
{
uint8_t v___x_362_; 
lean_dec(v_val_360_);
v___x_362_ = lean_unbox(v_defValue_356_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_363_, lean_object* v_opt_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_opts_363_, v_opt_364_);
lean_dec_ref(v_opt_364_);
lean_dec_ref(v_opts_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1));
v___x_371_ = l_Lean_MessageData_ofFormat(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object* v_msgData_372_, lean_object* v_macroStack_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_options_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_options_376_ = lean_ctor_get(v___y_374_, 2);
v___x_377_ = l_Lean_Elab_pp_macroStack;
v___x_378_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_macroStack_373_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_msgData_372_);
return v___x_379_;
}
else
{
if (lean_obj_tag(v_macroStack_373_) == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v_msgData_372_);
return v___x_380_;
}
else
{
lean_object* v_head_381_; lean_object* v_after_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_397_; 
v_head_381_ = lean_ctor_get(v_macroStack_373_, 0);
lean_inc(v_head_381_);
v_after_382_ = lean_ctor_get(v_head_381_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_head_381_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_head_381_, 0);
lean_dec(v_unused_398_);
v___x_384_ = v_head_381_;
v_isShared_385_ = v_isSharedCheck_397_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_after_382_);
lean_dec(v_head_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_397_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 7);
lean_ctor_set(v___x_384_, 1, v___x_386_);
lean_ctor_set(v___x_384_, 0, v_msgData_372_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_msgData_372_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_396_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_msgData_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_389_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_MessageData_ofSyntax(v_after_382_);
v___x_392_ = l_Lean_indentD(v___x_391_);
v_msgData_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_393_, 0, v___x_390_);
lean_ctor_set(v_msgData_393_, 1, v___x_392_);
v___x_394_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(v_msgData_393_, v_macroStack_373_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_399_, lean_object* v_macroStack_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_399_, v_macroStack_400_, v___y_401_);
lean_dec_ref(v___y_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v_macroStack_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_ref_412_ = lean_ctor_get(v___y_409_, 5);
v___x_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_404_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref(v___x_413_);
v_macroStack_415_ = lean_ctor_get(v___y_405_, 1);
v___x_416_ = l_Lean_Elab_getBetterRef(v_ref_412_, v_macroStack_415_);
lean_inc(v_macroStack_415_);
v___x_417_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_414_, v_macroStack_415_, v___y_409_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_416_);
lean_ctor_set(v___x_422_, 1, v_a_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 1);
lean_ctor_set(v___x_420_, 0, v___x_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_435_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Array_mkArray0(lean_box(0));
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_483_ = l_String_toRawSubstring_x27(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_530_, lean_object* v_decl_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
if (lean_obj_tag(v_letOrReassign_530_) == 2)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_531_);
v___x_540_ = l_Lean_Syntax_isOfKind(v_decl_531_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_542_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_543_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = l_Lean_Syntax_getArg(v_decl_531_, v___x_545_);
v___x_547_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_546_);
v___x_548_ = l_Lean_Syntax_isOfKind(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___y_551_; lean_object* v_pattern_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___x_621_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_546_);
v___x_621_ = l_Lean_Syntax_isOfKind(v___x_546_, v___x_549_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_546_);
v___x_622_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_623_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_624_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = l_Lean_Syntax_getArg(v___x_546_, v___x_626_);
v___x_628_ = l_Lean_Syntax_matchesNull(v___x_627_, v___x_545_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v___x_546_);
v___x_629_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_630_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_631_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_632_;
}
else
{
lean_object* v_pattern_633_; lean_object* v_xType_x3f_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_pattern_633_ = l_Lean_Syntax_getArg(v___x_546_, v___x_545_);
v___x_668_ = lean_unsigned_to_nat(2u);
v___x_669_ = l_Lean_Syntax_getArg(v___x_546_, v___x_668_);
v___x_670_ = l_Lean_Syntax_isNone(v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
lean_inc(v___x_669_);
v___x_671_ = l_Lean_Syntax_matchesNull(v___x_669_, v___x_626_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v___x_669_);
lean_dec(v_pattern_633_);
lean_dec(v___x_546_);
v___x_672_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_673_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_674_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_676_ = l_Lean_Syntax_getArg(v___x_669_, v___x_545_);
lean_dec(v___x_669_);
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_676_);
v___x_678_ = l_Lean_Syntax_isOfKind(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v___x_676_);
lean_dec(v_pattern_633_);
lean_dec(v___x_546_);
v___x_679_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_680_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_681_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_682_;
}
else
{
lean_object* v_xType_x3f_683_; lean_object* v___x_684_; 
lean_dec(v_decl_531_);
v_xType_x3f_683_ = l_Lean_Syntax_getArg(v___x_676_, v___x_626_);
lean_dec(v___x_676_);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_xType_x3f_683_);
v_xType_x3f_635_ = v___x_684_;
v___y_636_ = v_a_532_;
v___y_637_ = v_a_533_;
v___y_638_ = v_a_534_;
v___y_639_ = v_a_535_;
v___y_640_ = v_a_536_;
v___y_641_ = v_a_537_;
goto v___jp_634_;
}
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v___x_669_);
lean_dec(v_decl_531_);
v___x_685_ = lean_box(0);
v_xType_x3f_635_ = v___x_685_;
v___y_636_ = v_a_532_;
v___y_637_ = v_a_533_;
v___y_638_ = v_a_534_;
v___y_639_ = v_a_535_;
v___y_640_ = v_a_536_;
v___y_641_ = v_a_537_;
goto v___jp_634_;
}
v___jp_634_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(4u);
v___x_643_ = l_Lean_Syntax_getArg(v___x_546_, v___x_642_);
lean_dec(v___x_546_);
if (lean_obj_tag(v_xType_x3f_635_) == 0)
{
v___y_551_ = v___x_643_;
v_pattern_552_ = v_pattern_633_;
v___y_553_ = v___y_636_;
v___y_554_ = v___y_637_;
v___y_555_ = v___y_638_;
v___y_556_ = v___y_639_;
v___y_557_ = v___y_640_;
v___y_558_ = v___y_641_;
goto v___jp_550_;
}
else
{
lean_object* v_val_644_; lean_object* v_ref_645_; lean_object* v_quotContext_646_; lean_object* v_currMacroScope_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_val_644_ = lean_ctor_get(v_xType_x3f_635_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v_xType_x3f_635_, 1);
v_ref_645_ = lean_ctor_get(v___y_640_, 5);
v_quotContext_646_ = lean_ctor_get(v___y_640_, 10);
v_currMacroScope_647_ = lean_ctor_get(v___y_640_, 11);
v___x_648_ = l_Lean_SourceInfo_fromRef(v_ref_645_, v___x_548_);
v___x_649_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_648_, 7);
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_654_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_655_ = lean_box(0);
lean_inc(v_currMacroScope_647_);
lean_inc(v_quotContext_646_);
v___x_656_ = l_Lean_addMacroScope(v_quotContext_646_, v___x_655_, v_currMacroScope_647_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_658_, 0, v___x_648_);
lean_ctor_set(v___x_658_, 1, v___x_654_);
lean_ctor_set(v___x_658_, 2, v___x_656_);
lean_ctor_set(v___x_658_, 3, v___x_657_);
v___x_659_ = l_Lean_Syntax_node1(v___x_648_, v___x_653_, v___x_658_);
v___x_660_ = l_Lean_Syntax_node2(v___x_648_, v___x_650_, v___x_652_, v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_648_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_664_ = l_Lean_Syntax_node1(v___x_648_, v___x_663_, v_val_644_);
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_648_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_Syntax_node5(v___x_648_, v___x_649_, v___x_660_, v_pattern_633_, v___x_662_, v___x_664_, v___x_666_);
v___y_551_ = v___x_643_;
v_pattern_552_ = v___x_667_;
v___y_553_ = v___y_636_;
v___y_554_ = v___y_637_;
v___y_555_ = v___y_638_;
v___y_556_ = v___y_639_;
v___y_557_ = v___y_640_;
v___y_558_ = v___y_641_;
goto v___jp_550_;
}
}
}
}
v___jp_550_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_box(v___x_540_);
v___x_561_ = lean_box(v___x_540_);
lean_inc(v_pattern_552_);
v___x_562_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_562_, 0, v_pattern_552_);
lean_closure_set(v___x_562_, 1, v___x_559_);
lean_closure_set(v___x_562_, 2, v___x_560_);
lean_closure_set(v___x_562_, 3, v___x_561_);
v___x_563_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_562_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
v___x_565_ = lean_infer_type(v_a_564_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = l_Lean_Elab_Term_exprToSyntax(v_a_566_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_604_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_604_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_604_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_604_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_ref_572_; lean_object* v_quotContext_573_; lean_object* v_currMacroScope_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v_ref_572_ = lean_ctor_get(v___y_557_, 5);
v_quotContext_573_ = lean_ctor_get(v___y_557_, 10);
v_currMacroScope_574_ = lean_ctor_get(v___y_557_, 11);
v___x_575_ = l_Lean_SourceInfo_fromRef(v_ref_572_, v___x_548_);
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_577_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_575_, 11);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_575_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_575_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_575_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_586_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_587_ = lean_box(0);
lean_inc(v_currMacroScope_574_);
lean_inc(v_quotContext_573_);
v___x_588_ = l_Lean_addMacroScope(v_quotContext_573_, v___x_587_, v_currMacroScope_574_);
v___x_589_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_590_, 0, v___x_575_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_588_);
lean_ctor_set(v___x_590_, 3, v___x_589_);
v___x_591_ = l_Lean_Syntax_node1(v___x_575_, v___x_585_, v___x_590_);
v___x_592_ = l_Lean_Syntax_node2(v___x_575_, v___x_582_, v___x_584_, v___x_591_);
v___x_593_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_575_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_Syntax_node1(v___x_575_, v___x_576_, v_a_568_);
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_575_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Syntax_node5(v___x_575_, v___x_581_, v___x_592_, v___y_551_, v___x_594_, v___x_595_, v___x_597_);
lean_inc_ref(v___x_578_);
v___x_599_ = l_Lean_Syntax_node5(v___x_575_, v___x_549_, v_pattern_552_, v___x_578_, v___x_578_, v___x_580_, v___x_598_);
v___x_600_ = l_Lean_Syntax_node1(v___x_575_, v___x_539_, v___x_599_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_600_);
v___x_602_ = v___x_570_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_dec(v_pattern_552_);
lean_dec(v___y_551_);
return v___x_567_;
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_pattern_552_);
lean_dec(v___y_551_);
v_a_605_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_565_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_565_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_pattern_552_);
lean_dec(v___y_551_);
v_a_613_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_563_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_563_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = l_Lean_Syntax_getArg(v___x_546_, v___x_545_);
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_686_);
v___x_688_ = l_Lean_Syntax_isOfKind(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_686_);
lean_dec(v___x_546_);
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_690_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_691_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_692_;
}
else
{
lean_object* v_x_693_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v_a_702_; lean_object* v_xType_x3f_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_x_693_ = l_Lean_Syntax_getArg(v___x_686_, v___x_545_);
lean_dec(v___x_686_);
v___x_779_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_693_);
v___x_780_ = l_Lean_Syntax_isOfKind(v_x_693_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v_x_693_);
lean_dec(v___x_546_);
v___x_781_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_782_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_783_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = l_Lean_Syntax_getArg(v___x_546_, v___x_785_);
v___x_787_ = l_Lean_Syntax_matchesNull(v___x_786_, v___x_545_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v_x_693_);
lean_dec(v___x_546_);
v___x_788_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_789_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_790_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(2u);
v___x_793_ = l_Lean_Syntax_getArg(v___x_546_, v___x_792_);
v___x_794_ = l_Lean_Syntax_isNone(v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Syntax_matchesNull(v___x_793_, v___x_785_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_793_);
lean_dec(v_x_693_);
lean_dec(v___x_546_);
v___x_796_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_797_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_798_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = l_Lean_Syntax_getArg(v___x_793_, v___x_545_);
lean_dec(v___x_793_);
v___x_801_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_800_);
v___x_802_ = l_Lean_Syntax_isOfKind(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___x_800_);
lean_dec(v_x_693_);
lean_dec(v___x_546_);
v___x_803_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_804_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_805_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_806_;
}
else
{
lean_object* v_xType_x3f_807_; lean_object* v___x_808_; 
lean_dec(v_decl_531_);
v_xType_x3f_807_ = l_Lean_Syntax_getArg(v___x_800_, v___x_785_);
lean_dec(v___x_800_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_xType_x3f_807_);
v_xType_x3f_751_ = v___x_808_;
v___y_752_ = v_a_532_;
v___y_753_ = v_a_533_;
v___y_754_ = v_a_534_;
v___y_755_ = v_a_535_;
v___y_756_ = v_a_536_;
v___y_757_ = v_a_537_;
goto v___jp_750_;
}
}
}
else
{
lean_object* v___x_809_; 
lean_dec(v___x_793_);
lean_dec(v_decl_531_);
v___x_809_ = lean_box(0);
v_xType_x3f_751_ = v___x_809_;
v___y_752_ = v_a_532_;
v___y_753_ = v_a_533_;
v___y_754_ = v_a_534_;
v___y_755_ = v_a_535_;
v___y_756_ = v_a_536_;
v___y_757_ = v_a_537_;
goto v___jp_750_;
}
}
}
v___jp_694_:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_box(0);
lean_inc(v_x_693_);
v___x_704_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_693_, v_a_702_, v___x_540_, v___x_540_, v___x_703_, v___y_701_, v___y_695_, v___y_698_, v___y_699_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref_known(v___x_704_, 1);
v___x_705_ = l_Lean_TSyntax_getId(v_x_693_);
v___x_706_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_705_, v___y_698_, v___y_699_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_LocalDecl_type(v_a_707_);
lean_dec(v_a_707_);
v___x_709_ = l_Lean_Elab_Term_exprToSyntax(v___x_708_, v___y_701_, v___y_695_, v___y_698_, v___y_699_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_733_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_ref_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_ref_714_ = lean_ctor_get(v___y_696_, 5);
v___x_715_ = 0;
v___x_716_ = l_Lean_SourceInfo_fromRef(v_ref_714_, v___x_715_);
lean_inc_n(v___x_716_, 7);
v___x_717_ = l_Lean_Syntax_node1(v___x_716_, v___x_687_, v_x_693_);
v___x_718_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_720_, 0, v___x_716_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
lean_ctor_set(v___x_720_, 2, v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_716_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_Syntax_node2(v___x_716_, v___x_721_, v___x_723_, v_a_710_);
v___x_725_ = l_Lean_Syntax_node1(v___x_716_, v___x_718_, v___x_724_);
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_716_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_Syntax_node5(v___x_716_, v___x_547_, v___x_717_, v___x_720_, v___x_725_, v___x_727_, v___y_700_);
v___x_729_ = l_Lean_Syntax_node1(v___x_716_, v___x_539_, v___x_728_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_729_);
v___x_731_ = v___x_712_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_dec(v___y_700_);
lean_dec(v_x_693_);
return v___x_709_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___y_700_);
lean_dec(v_x_693_);
v_a_734_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_706_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_706_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v___y_700_);
lean_dec(v_x_693_);
v_a_742_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_704_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_704_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
v___jp_750_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(4u);
v___x_759_ = l_Lean_Syntax_getArg(v___x_546_, v___x_758_);
lean_dec(v___x_546_);
if (lean_obj_tag(v_xType_x3f_751_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_box(0);
v___y_695_ = v___y_753_;
v___y_696_ = v___y_756_;
v___y_697_ = v___y_757_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_755_;
v___y_700_ = v___x_759_;
v___y_701_ = v___y_752_;
v_a_702_ = v___x_760_;
goto v___jp_694_;
}
else
{
lean_object* v_val_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_778_; 
v_val_761_ = lean_ctor_get(v_xType_x3f_751_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_xType_x3f_751_);
if (v_isSharedCheck_778_ == 0)
{
v___x_763_ = v_xType_x3f_751_;
v_isShared_764_ = v_isSharedCheck_778_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_val_761_);
lean_dec(v_xType_x3f_751_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_778_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Elab_Term_elabType(v_val_761_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_a_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v___y_695_ = v___y_753_;
v___y_696_ = v___y_756_;
v___y_697_ = v___y_757_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_755_;
v___y_700_ = v___x_759_;
v___y_701_ = v___y_752_;
v_a_702_ = v___x_768_;
goto v___jp_694_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_763_);
lean_dec(v___x_759_);
lean_dec(v_x_693_);
v_a_770_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_765_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
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
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_decl_531_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_811_, lean_object* v_decl_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_811_, v_decl_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_letOrReassign_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_821_, lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_831_, lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_831_, v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_841_, lean_object* v_macroStack_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_841_, v_macroStack_842_, v___y_847_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_851_, lean_object* v_macroStack_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_851_, v_macroStack_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_ref_867_; lean_object* v___x_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_ref_867_ = lean_ctor_get(v___y_864_, 5);
v___x_868_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_ref_867_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_ref_867_);
lean_ctor_set(v___x_873_, 1, v_a_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 1);
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
uint8_t v_postponeValue_900_; uint8_t v_generalize_901_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; 
v_postponeValue_900_ = lean_ctor_get_uint8(v_config_891_, sizeof(void*)*1 + 3);
v_generalize_901_ = lean_ctor_get_uint8(v_config_891_, sizeof(void*)*1 + 4);
if (v_postponeValue_900_ == 0)
{
v___y_903_ = v_a_892_;
v___y_904_ = v_a_893_;
v___y_905_ = v_a_894_;
v___y_906_ = v_a_895_;
v___y_907_ = v_a_896_;
v___y_908_ = v_a_897_;
v___y_909_ = v_a_898_;
goto v___jp_902_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_915_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_914_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_915_;
}
v___jp_902_:
{
if (v_generalize_901_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_913_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_912_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec_ref(v_config_916_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_926_, lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_927_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_937_, lean_object* v_msg_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_937_, v_msg_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_box(0);
v___x_949_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_keyedConfig_985_; uint8_t v_trackZetaDelta_986_; lean_object* v_zetaDeltaSet_987_; lean_object* v_localInstances_988_; lean_object* v_defEqCtx_x3f_989_; lean_object* v_synthPendingDepth_990_; lean_object* v_customCanUnfoldPredicate_x3f_991_; uint8_t v_univApprox_992_; uint8_t v_inTypeClassResolution_993_; uint8_t v_cacheInferType_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_keyedConfig_985_ = lean_ctor_get(v___y_980_, 0);
v_trackZetaDelta_986_ = lean_ctor_get_uint8(v___y_980_, sizeof(void*)*7);
v_zetaDeltaSet_987_ = lean_ctor_get(v___y_980_, 1);
v_localInstances_988_ = lean_ctor_get(v___y_980_, 3);
v_defEqCtx_x3f_989_ = lean_ctor_get(v___y_980_, 4);
v_synthPendingDepth_990_ = lean_ctor_get(v___y_980_, 5);
v_customCanUnfoldPredicate_x3f_991_ = lean_ctor_get(v___y_980_, 6);
v_univApprox_992_ = lean_ctor_get_uint8(v___y_980_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_993_ = lean_ctor_get_uint8(v___y_980_, sizeof(void*)*7 + 2);
v_cacheInferType_994_ = lean_ctor_get_uint8(v___y_980_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_991_);
lean_inc(v_synthPendingDepth_990_);
lean_inc(v_defEqCtx_x3f_989_);
lean_inc_ref(v_localInstances_988_);
lean_inc(v_zetaDeltaSet_987_);
lean_inc_ref(v_keyedConfig_985_);
v___x_995_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_995_, 0, v_keyedConfig_985_);
lean_ctor_set(v___x_995_, 1, v_zetaDeltaSet_987_);
lean_ctor_set(v___x_995_, 2, v_lctx_976_);
lean_ctor_set(v___x_995_, 3, v_localInstances_988_);
lean_ctor_set(v___x_995_, 4, v_defEqCtx_x3f_989_);
lean_ctor_set(v___x_995_, 5, v_synthPendingDepth_990_);
lean_ctor_set(v___x_995_, 6, v_customCanUnfoldPredicate_x3f_991_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*7, v_trackZetaDelta_986_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*7 + 1, v_univApprox_992_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*7 + 2, v_inTypeClassResolution_993_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*7 + 3, v_cacheInferType_994_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_996_ = lean_apply_7(v_x_977_, v___y_978_, v___y_979_, v___x_995_, v___y_981_, v___y_982_, v___y_983_, lean_box(0));
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1015_, lean_object* v_lctx_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1016_, v_x_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_lctx_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1026_, v_lctx_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc_ref(v___y_1038_);
v___x_1047_ = lean_apply_9(v_k_1037_, v_b_1041_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, lean_box(0));
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v_b_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1059_, lean_object* v_type_1060_, lean_object* v_val_1061_, lean_object* v_k_1062_, uint8_t v_nondep_1063_, uint8_t v_kind_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___f_1073_; lean_object* v___x_1074_; 
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc_ref(v___y_1065_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1073_, 0, v_k_1062_);
lean_closure_set(v___f_1073_, 1, v___y_1065_);
lean_closure_set(v___f_1073_, 2, v___y_1066_);
lean_closure_set(v___f_1073_, 3, v___y_1067_);
v___x_1074_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1059_, v_type_1060_, v_val_1061_, v___f_1073_, v_nondep_1063_, v_kind_1064_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1074_) == 0)
{
return v___x_1074_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1083_, lean_object* v_type_1084_, lean_object* v_val_1085_, lean_object* v_k_1086_, lean_object* v_nondep_1087_, lean_object* v_kind_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_nondep_boxed_1097_; uint8_t v_kind_boxed_1098_; lean_object* v_res_1099_; 
v_nondep_boxed_1097_ = lean_unbox(v_nondep_1087_);
v_kind_boxed_1098_ = lean_unbox(v_kind_1088_);
v_res_1099_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1083_, v_type_1084_, v_val_1085_, v_k_1086_, v_nondep_boxed_1097_, v_kind_boxed_1098_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1100_, lean_object* v_name_1101_, lean_object* v_type_1102_, lean_object* v_val_1103_, lean_object* v_k_1104_, uint8_t v_nondep_1105_, uint8_t v_kind_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1101_, v_type_1102_, v_val_1103_, v_k_1104_, v_nondep_1105_, v_kind_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_name_1117_, lean_object* v_type_1118_, lean_object* v_val_1119_, lean_object* v_k_1120_, lean_object* v_nondep_1121_, lean_object* v_kind_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_nondep_boxed_1131_; uint8_t v_kind_boxed_1132_; lean_object* v_res_1133_; 
v_nondep_boxed_1131_ = lean_unbox(v_nondep_1121_);
v_kind_boxed_1132_ = lean_unbox(v_kind_1122_);
v_res_1133_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1116_, v_name_1117_, v_type_1118_, v_val_1119_, v_k_1120_, v_nondep_boxed_1131_, v_kind_boxed_1132_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1134_, lean_object* v___x_1135_, uint8_t v___x_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, uint8_t v___x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1134_, v___x_1135_, v___x_1136_, v___x_1136_, v___x_1137_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = 1;
v___x_1150_ = l_Lean_Meta_mkLambdaFVars(v___x_1138_, v_a_1148_, v___x_1139_, v___x_1139_, v___x_1139_, v___x_1136_, v___x_1149_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1150_;
}
else
{
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_98869__boxed_1164_; uint8_t v___x_98872__boxed_1165_; lean_object* v_res_1166_; 
v___x_98869__boxed_1164_ = lean_unbox(v___x_1153_);
v___x_98872__boxed_1165_ = lean_unbox(v___x_1156_);
v_res_1166_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1151_, v___x_1152_, v___x_98869__boxed_1164_, v___x_1154_, v___x_1155_, v___x_98872__boxed_1165_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v___x_1155_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
lean_object* v_ks_1171_; lean_object* v_vs_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1196_; 
v_ks_1171_ = lean_ctor_get(v_x_1167_, 0);
v_vs_1172_ = lean_ctor_get(v_x_1167_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_x_1167_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1174_ = v_x_1167_;
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_vs_1172_);
lean_inc(v_ks_1171_);
lean_dec(v_x_1167_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_array_get_size(v_ks_1171_);
v___x_1177_ = lean_nat_dec_lt(v_x_1168_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
lean_dec(v_x_1168_);
v___x_1178_ = lean_array_push(v_ks_1171_, v_x_1169_);
v___x_1179_ = lean_array_push(v_vs_1172_, v_x_1170_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1179_);
lean_ctor_set(v___x_1174_, 0, v___x_1178_);
v___x_1181_ = v___x_1174_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
else
{
lean_object* v_k_x27_1183_; uint8_t v___x_1184_; 
v_k_x27_1183_ = lean_array_fget_borrowed(v_ks_1171_, v_x_1168_);
v___x_1184_ = l_Lean_instBEqFVarId_beq(v_x_1169_, v_k_x27_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1186_; 
if (v_isShared_1175_ == 0)
{
v___x_1186_ = v___x_1174_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_ks_1171_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_vs_1172_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_x_1168_, v___x_1187_);
lean_dec(v_x_1168_);
v_x_1167_ = v___x_1186_;
v_x_1168_ = v___x_1188_;
goto _start;
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = lean_array_fset(v_ks_1171_, v_x_1168_, v_x_1169_);
v___x_1192_ = lean_array_fset(v_vs_1172_, v_x_1168_, v_x_1170_);
lean_dec(v_x_1168_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1192_);
lean_ctor_set(v___x_1174_, 0, v___x_1191_);
v___x_1194_ = v___x_1174_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1197_, lean_object* v_k_1198_, lean_object* v_v_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1197_, v___x_1200_, v_k_1198_, v_v_1199_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1203_, size_t v_x_1204_, size_t v_x_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
lean_object* v_es_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v_j_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_es_1208_ = lean_ctor_get(v_x_1203_, 0);
v___x_1209_ = ((size_t)31ULL);
v___x_1210_ = lean_usize_land(v_x_1204_, v___x_1209_);
v_j_1211_ = lean_usize_to_nat(v___x_1210_);
v___x_1212_ = lean_array_get_size(v_es_1208_);
v___x_1213_ = lean_nat_dec_lt(v_j_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_j_1211_);
lean_dec(v_x_1207_);
lean_dec(v_x_1206_);
return v_x_1203_;
}
else
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1252_; 
lean_inc_ref(v_es_1208_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_x_1203_, 0);
lean_dec(v_unused_1253_);
v___x_1215_ = v_x_1203_;
v_isShared_1216_ = v_isSharedCheck_1252_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v_x_1203_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1252_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_v_1217_; lean_object* v___x_1218_; lean_object* v_xs_x27_1219_; lean_object* v___y_1221_; 
v_v_1217_ = lean_array_fget(v_es_1208_, v_j_1211_);
v___x_1218_ = lean_box(0);
v_xs_x27_1219_ = lean_array_fset(v_es_1208_, v_j_1211_, v___x_1218_);
switch(lean_obj_tag(v_v_1217_))
{
case 0:
{
lean_object* v_key_1226_; lean_object* v_val_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1237_; 
v_key_1226_ = lean_ctor_get(v_v_1217_, 0);
v_val_1227_ = lean_ctor_get(v_v_1217_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_v_1217_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1229_ = v_v_1217_;
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_val_1227_);
lean_inc(v_key_1226_);
lean_dec(v_v_1217_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
uint8_t v___x_1231_; 
v___x_1231_ = l_Lean_instBEqFVarId_beq(v_x_1206_, v_key_1226_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_del_object(v___x_1229_);
v___x_1232_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1226_, v_val_1227_, v_x_1206_, v_x_1207_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
v___y_1221_ = v___x_1233_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1235_; 
lean_dec(v_val_1227_);
lean_dec(v_key_1226_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_x_1207_);
lean_ctor_set(v___x_1229_, 0, v_x_1206_);
v___x_1235_ = v___x_1229_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_x_1206_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_x_1207_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
v___y_1221_ = v___x_1235_;
goto v___jp_1220_;
}
}
}
}
case 1:
{
lean_object* v_node_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1250_; 
v_node_1238_ = lean_ctor_get(v_v_1217_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_v_1217_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1240_ = v_v_1217_;
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_node_1238_);
lean_dec(v_v_1217_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1242_ = ((size_t)5ULL);
v___x_1243_ = lean_usize_shift_right(v_x_1204_, v___x_1242_);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_add(v_x_1205_, v___x_1244_);
v___x_1246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1238_, v___x_1243_, v___x_1245_, v_x_1206_, v_x_1207_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1246_);
v___x_1248_ = v___x_1240_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
v___y_1221_ = v___x_1248_;
goto v___jp_1220_;
}
}
}
default: 
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_x_1206_);
lean_ctor_set(v___x_1251_, 1, v_x_1207_);
v___y_1221_ = v___x_1251_;
goto v___jp_1220_;
}
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_array_fset(v_xs_x27_1219_, v_j_1211_, v___y_1221_);
lean_dec(v_j_1211_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1222_);
v___x_1224_ = v___x_1215_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v_ks_1254_; lean_object* v_vs_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1275_; 
v_ks_1254_ = lean_ctor_get(v_x_1203_, 0);
v_vs_1255_ = lean_ctor_get(v_x_1203_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1257_ = v_x_1203_;
v_isShared_1258_ = v_isSharedCheck_1275_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_vs_1255_);
lean_inc(v_ks_1254_);
lean_dec(v_x_1203_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1275_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ks_1254_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_vs_1255_);
v___x_1260_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v_newNode_1261_; uint8_t v___y_1263_; size_t v___x_1269_; uint8_t v___x_1270_; 
v_newNode_1261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1260_, v_x_1206_, v_x_1207_);
v___x_1269_ = ((size_t)7ULL);
v___x_1270_ = lean_usize_dec_le(v___x_1269_, v_x_1205_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1261_);
v___x_1272_ = lean_unsigned_to_nat(4u);
v___x_1273_ = lean_nat_dec_lt(v___x_1271_, v___x_1272_);
lean_dec(v___x_1271_);
v___y_1263_ = v___x_1273_;
goto v___jp_1262_;
}
else
{
v___y_1263_ = v___x_1270_;
goto v___jp_1262_;
}
v___jp_1262_:
{
if (v___y_1263_ == 0)
{
lean_object* v_ks_1264_; lean_object* v_vs_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_ks_1264_ = lean_ctor_get(v_newNode_1261_, 0);
lean_inc_ref(v_ks_1264_);
v_vs_1265_ = lean_ctor_get(v_newNode_1261_, 1);
lean_inc_ref(v_vs_1265_);
lean_dec_ref(v_newNode_1261_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1205_, v_ks_1264_, v_vs_1265_, v___x_1266_, v___x_1267_);
lean_dec_ref(v_vs_1265_);
lean_dec_ref(v_ks_1264_);
return v___x_1268_;
}
else
{
return v_newNode_1261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1276_, lean_object* v_keys_1277_, lean_object* v_vals_1278_, lean_object* v_i_1279_, lean_object* v_entries_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_array_get_size(v_keys_1277_);
v___x_1282_ = lean_nat_dec_lt(v_i_1279_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v_i_1279_);
return v_entries_1280_;
}
else
{
lean_object* v_k_1283_; lean_object* v_v_1284_; uint64_t v___x_1285_; size_t v_h_1286_; size_t v___x_1287_; lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v_h_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_k_1283_ = lean_array_fget_borrowed(v_keys_1277_, v_i_1279_);
v_v_1284_ = lean_array_fget_borrowed(v_vals_1278_, v_i_1279_);
v___x_1285_ = l_Lean_instHashableFVarId_hash(v_k_1283_);
v_h_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = ((size_t)5ULL);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_sub(v_depth_1276_, v___x_1289_);
v___x_1291_ = lean_usize_mul(v___x_1287_, v___x_1290_);
v_h_1292_ = lean_usize_shift_right(v_h_1286_, v___x_1291_);
v___x_1293_ = lean_nat_add(v_i_1279_, v___x_1288_);
lean_dec(v_i_1279_);
lean_inc(v_v_1284_);
lean_inc(v_k_1283_);
v___x_1294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1280_, v_h_1292_, v_depth_1276_, v_k_1283_, v_v_1284_);
v_i_1279_ = v___x_1293_;
v_entries_1280_ = v___x_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_i_1299_, lean_object* v_entries_1300_){
_start:
{
size_t v_depth_boxed_1301_; lean_object* v_res_1302_; 
v_depth_boxed_1301_ = lean_unbox_usize(v_depth_1296_);
lean_dec(v_depth_1296_);
v_res_1302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1301_, v_keys_1297_, v_vals_1298_, v_i_1299_, v_entries_1300_);
lean_dec_ref(v_vals_1298_);
lean_dec_ref(v_keys_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
size_t v_x_98992__boxed_1308_; size_t v_x_98993__boxed_1309_; lean_object* v_res_1310_; 
v_x_98992__boxed_1308_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_x_98993__boxed_1309_ = lean_unbox_usize(v_x_1305_);
lean_dec(v_x_1305_);
v_res_1310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1303_, v_x_98992__boxed_1308_, v_x_98993__boxed_1309_, v_x_1306_, v_x_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
uint64_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = l_Lean_instHashableFVarId_hash(v_x_1312_);
v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1311_, v___x_1315_, v___x_1316_, v_x_1312_, v_x_1313_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1318_, size_t v_i_1319_, size_t v_stop_1320_, lean_object* v_b_1321_){
_start:
{
lean_object* v___y_1323_; uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_eq(v_i_1319_, v_stop_1320_);
if (v___x_1327_ == 0)
{
lean_object* v_fvarIdToDecl_1328_; lean_object* v_decls_1329_; lean_object* v_auxDeclToFullName_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_fvarIdToDecl_1328_ = lean_ctor_get(v_b_1321_, 0);
v_decls_1329_ = lean_ctor_get(v_b_1321_, 1);
v_auxDeclToFullName_1330_ = lean_ctor_get(v_b_1321_, 2);
v___x_1331_ = lean_array_uget_borrowed(v_as_1318_, v_i_1319_);
v___x_1332_ = l_Lean_Expr_fvarId_x21(v___x_1331_);
lean_inc_ref(v_b_1321_);
v___x_1333_ = lean_local_ctx_find(v_b_1321_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
v___y_1323_ = v_b_1321_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1360_; 
lean_inc(v_auxDeclToFullName_1330_);
lean_inc_ref(v_decls_1329_);
lean_inc_ref(v_fvarIdToDecl_1328_);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_b_1321_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1361_ = lean_ctor_get(v_b_1321_, 2);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_b_1321_, 1);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_b_1321_, 0);
lean_dec(v_unused_1363_);
v___x_1335_ = v_b_1321_;
v_isShared_1336_ = v_isSharedCheck_1360_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v_b_1321_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1360_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_val_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1359_; 
v_val_1337_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1339_ = v___x_1333_;
v_isShared_1340_ = v_isSharedCheck_1359_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_val_1337_);
lean_dec(v___x_1333_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1359_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1355_; lean_object* v_fvarId_1358_; 
v___x_1341_ = l_Lean_LocalDecl_type(v_val_1337_);
v___x_1342_ = l_Lean_Expr_cleanupAnnotations(v___x_1341_);
v___x_1343_ = l_Lean_LocalDecl_setType(v_val_1337_, v___x_1342_);
v_fvarId_1358_ = lean_ctor_get(v___x_1343_, 1);
lean_inc(v_fvarId_1358_);
v___y_1355_ = v_fvarId_1358_;
goto v___jp_1354_;
v___jp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1343_);
v___x_1348_ = v___x_1339_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1343_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = l_Lean_PersistentArray_set___redArg(v_decls_1329_, v___y_1346_, v___x_1348_);
lean_dec(v___y_1346_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v___x_1349_);
lean_ctor_set(v___x_1335_, 0, v___y_1345_);
v___x_1351_ = v___x_1335_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___y_1345_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_auxDeclToFullName_1330_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v___y_1323_ = v___x_1351_;
goto v___jp_1322_;
}
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; lean_object* v_index_1357_; 
lean_inc_ref(v___x_1343_);
v___x_1356_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1328_, v___y_1355_, v___x_1343_);
v_index_1357_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_index_1357_);
v___y_1345_ = v___x_1356_;
v___y_1346_ = v_index_1357_;
goto v___jp_1344_;
}
}
}
}
}
else
{
return v_b_1321_;
}
v___jp_1322_:
{
size_t v___x_1324_; size_t v___x_1325_; 
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_add(v_i_1319_, v___x_1324_);
v_i_1319_ = v___x_1325_;
v_b_1321_ = v___y_1323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1364_, lean_object* v_i_1365_, lean_object* v_stop_1366_, lean_object* v_b_1367_){
_start:
{
size_t v_i_boxed_1368_; size_t v_stop_boxed_1369_; lean_object* v_res_1370_; 
v_i_boxed_1368_ = lean_unbox_usize(v_i_1365_);
lean_dec(v_i_1365_);
v_stop_boxed_1369_ = lean_unbox_usize(v_stop_1366_);
lean_dec(v_stop_1366_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1364_, v_i_boxed_1368_, v_stop_boxed_1369_, v_b_1367_);
lean_dec_ref(v_as_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1371_, size_t v_i_1372_, lean_object* v_bs_1373_){
_start:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_usize_dec_lt(v_i_1372_, v_sz_1371_);
if (v___x_1374_ == 0)
{
return v_bs_1373_;
}
else
{
lean_object* v_v_1375_; lean_object* v_snd_1376_; lean_object* v___x_1377_; lean_object* v_bs_x27_1378_; size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v_v_1375_ = lean_array_uget_borrowed(v_bs_1373_, v_i_1372_);
v_snd_1376_ = lean_ctor_get(v_v_1375_, 1);
lean_inc(v_snd_1376_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v_bs_x27_1378_ = lean_array_uset(v_bs_1373_, v_i_1372_, v___x_1377_);
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1372_, v___x_1379_);
v___x_1381_ = lean_array_uset(v_bs_x27_1378_, v_i_1372_, v_snd_1376_);
v_i_1372_ = v___x_1380_;
v_bs_1373_ = v___x_1381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_bs_1385_){
_start:
{
size_t v_sz_boxed_1386_; size_t v_i_boxed_1387_; lean_object* v_res_1388_; 
v_sz_boxed_1386_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1386_, v_i_boxed_1387_, v_bs_1385_);
return v_res_1388_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1394_ = l_Lean_stringToMessageData(v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1400_, lean_object* v_value_1401_, uint8_t v___x_1402_, uint8_t v___x_1403_, lean_object* v___x_1404_, uint8_t v___y_1405_, lean_object* v_xs_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; 
lean_inc(v_type_1400_);
v___x_1414_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1414_, 0, v_type_1400_);
v___x_1415_ = 2;
v___x_1416_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1414_, v___x_1415_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; size_t v_sz_1418_; size_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___y_1422_; lean_object* v___y_1458_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v_sz_1418_ = lean_array_size(v_xs_1406_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1418_, v___x_1419_, v_xs_1406_);
if (v___y_1405_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1458_ = v___x_1494_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1458_ = v___x_1495_;
goto v___jp_1457_;
}
v___jp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; 
lean_inc(v_a_1417_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_a_1417_);
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_box(v___x_1402_);
v___x_1426_ = lean_box(v___x_1403_);
lean_inc_ref(v___x_1420_);
v___f_1427_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1427_, 0, v_value_1401_);
lean_closure_set(v___f_1427_, 1, v___x_1423_);
lean_closure_set(v___f_1427_, 2, v___x_1425_);
lean_closure_set(v___f_1427_, 3, v___x_1424_);
lean_closure_set(v___f_1427_, 4, v___x_1420_);
lean_closure_set(v___f_1427_, 5, v___x_1426_);
v___x_1428_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1422_, v___f_1427_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = 1;
v___x_1431_ = l_Lean_Meta_mkForallFVars(v___x_1420_, v_a_1417_, v___x_1403_, v___x_1402_, v___x_1402_, v___x_1430_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec_ref(v___x_1420_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1432_);
lean_ctor_set(v___x_1436_, 1, v_a_1429_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_a_1429_);
v_a_1441_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1431_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1431_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v___x_1420_);
lean_dec(v_a_1417_);
v_a_1449_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1428_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1428_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
v___jp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1458_);
v___x_1460_ = l_Lean_stringToMessageData(v___y_1458_);
lean_inc_ref(v___x_1460_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_inc(v_type_1400_);
v___x_1464_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1417_, v_type_1400_, v___x_1463_, v___y_1408_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref_known(v___x_1464_, 1);
v___x_1465_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___x_1460_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1462_);
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_inc(v_a_1417_);
v___x_1469_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1417_, v_type_1400_, v___x_1468_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_lctx_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
lean_dec_ref_known(v___x_1469_, 1);
v_lctx_1470_ = lean_ctor_get(v___y_1409_, 2);
v___x_1471_ = lean_array_get_size(v___x_1420_);
v___x_1472_ = lean_nat_dec_lt(v___x_1404_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_inc_ref(v_lctx_1470_);
v___y_1422_ = v_lctx_1470_;
goto v___jp_1421_;
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_nat_dec_le(v___x_1471_, v___x_1471_);
if (v___x_1473_ == 0)
{
if (v___x_1472_ == 0)
{
lean_inc_ref(v_lctx_1470_);
v___y_1422_ = v_lctx_1470_;
goto v___jp_1421_;
}
else
{
size_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_usize_of_nat(v___x_1471_);
lean_inc_ref(v_lctx_1470_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1420_, v___x_1419_, v___x_1474_, v_lctx_1470_);
v___y_1422_ = v___x_1475_;
goto v___jp_1421_;
}
}
else
{
size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_usize_of_nat(v___x_1471_);
lean_inc_ref(v_lctx_1470_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1420_, v___x_1419_, v___x_1476_, v_lctx_1470_);
v___y_1422_ = v___x_1477_;
goto v___jp_1421_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v___x_1420_);
lean_dec(v_a_1417_);
lean_dec(v_value_1401_);
v_a_1478_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1469_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1469_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1420_);
lean_dec(v_a_1417_);
lean_dec(v_value_1401_);
lean_dec(v_type_1400_);
v_a_1486_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1464_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1464_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v_xs_1406_);
lean_dec(v_value_1401_);
lean_dec(v_type_1400_);
v_a_1496_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1416_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1416_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1504_, lean_object* v_value_1505_, lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, lean_object* v___y_1509_, lean_object* v_xs_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_99305__boxed_1518_; uint8_t v___x_99306__boxed_1519_; uint8_t v___y_99308__boxed_1520_; lean_object* v_res_1521_; 
v___x_99305__boxed_1518_ = lean_unbox(v___x_1506_);
v___x_99306__boxed_1519_ = lean_unbox(v___x_1507_);
v___y_99308__boxed_1520_ = lean_unbox(v___y_1509_);
v_res_1521_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1504_, v_value_1505_, v___x_99305__boxed_1518_, v___x_99306__boxed_1519_, v___x_1508_, v___y_99308__boxed_1520_, v_xs_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___x_1508_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1522_, lean_object* v_a_1523_, uint8_t v_zeta_1524_, uint8_t v___y_1525_, lean_object* v_x_1526_, uint8_t v_usedOnly_1527_, uint8_t v___x_1528_, uint8_t v___x_1529_, lean_object* v_snd_1530_, lean_object* v_h_x27_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
lean_inc_ref(v_h_x27_1531_);
v___x_1540_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1522_, v_h_x27_1531_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1540_, 1);
v___x_1541_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1523_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
if (v_zeta_1524_ == 0)
{
if (v___y_1525_ == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref(v_snd_1530_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = lean_unsigned_to_nat(2u);
v___x_1544_ = lean_mk_empty_array_with_capacity(v___x_1543_);
v___x_1545_ = lean_array_push(v___x_1544_, v_x_1526_);
v___x_1546_ = lean_array_push(v___x_1545_, v_h_x27_1531_);
v___x_1547_ = 1;
v___x_1548_ = l_Lean_Meta_mkLetFVars(v___x_1546_, v_a_1542_, v_usedOnly_1527_, v___x_1528_, v___x_1547_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___x_1546_);
return v___x_1548_;
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1549_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1550_ = lean_unsigned_to_nat(2u);
v___x_1551_ = lean_mk_empty_array_with_capacity(v___x_1550_);
v___x_1552_ = lean_array_push(v___x_1551_, v_x_1526_);
v___x_1553_ = lean_array_push(v___x_1552_, v_h_x27_1531_);
v___x_1554_ = 1;
v___x_1555_ = l_Lean_Meta_mkLambdaFVars(v___x_1553_, v_a_1549_, v___x_1528_, v___x_1529_, v___x_1528_, v___x_1529_, v___x_1554_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
lean_inc_ref(v_snd_1530_);
v___x_1557_ = l_Lean_Meta_mkEqRefl(v_snd_1530_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1566_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = l_Lean_mkAppB(v_a_1556_, v_snd_1530_, v_a_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_dec(v_a_1556_);
lean_dec_ref(v_snd_1530_);
return v___x_1557_;
}
}
else
{
lean_dec_ref(v_snd_1530_);
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1567_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1568_ = lean_unsigned_to_nat(2u);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = lean_array_push(v___x_1569_, v_x_1526_);
v___x_1571_ = lean_array_push(v___x_1570_, v_h_x27_1531_);
v___x_1572_ = l_Lean_Expr_abstractM(v_a_1567_, v___x_1571_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___x_1571_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
lean_inc_ref(v_snd_1530_);
v___x_1574_ = l_Lean_Meta_mkEqRefl(v_snd_1530_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1585_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1585_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1585_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1579_ = lean_array_push(v___x_1569_, v_snd_1530_);
v___x_1580_ = lean_array_push(v___x_1579_, v_a_1575_);
v___x_1581_ = lean_expr_instantiate_rev(v_a_1573_, v___x_1580_);
lean_dec_ref(v___x_1580_);
lean_dec(v_a_1573_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_dec(v_a_1573_);
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_snd_1530_);
return v___x_1574_;
}
}
else
{
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_snd_1530_);
return v___x_1572_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1531_);
lean_dec_ref(v_snd_1530_);
lean_dec_ref(v_x_1526_);
return v___x_1541_;
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_h_x27_1531_);
lean_dec_ref(v_snd_1530_);
lean_dec_ref(v_x_1526_);
lean_dec_ref(v_a_1523_);
v_a_1586_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1540_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1540_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1594_ = _args[0];
lean_object* v_a_1595_ = _args[1];
lean_object* v_zeta_1596_ = _args[2];
lean_object* v___y_1597_ = _args[3];
lean_object* v_x_1598_ = _args[4];
lean_object* v_usedOnly_1599_ = _args[5];
lean_object* v___x_1600_ = _args[6];
lean_object* v___x_1601_ = _args[7];
lean_object* v_snd_1602_ = _args[8];
lean_object* v_h_x27_1603_ = _args[9];
lean_object* v___y_1604_ = _args[10];
lean_object* v___y_1605_ = _args[11];
lean_object* v___y_1606_ = _args[12];
lean_object* v___y_1607_ = _args[13];
lean_object* v___y_1608_ = _args[14];
lean_object* v___y_1609_ = _args[15];
lean_object* v___y_1610_ = _args[16];
lean_object* v___y_1611_ = _args[17];
_start:
{
uint8_t v_zeta_boxed_1612_; uint8_t v___y_99532__boxed_1613_; uint8_t v_usedOnly_boxed_1614_; uint8_t v___x_99533__boxed_1615_; uint8_t v___x_99534__boxed_1616_; lean_object* v_res_1617_; 
v_zeta_boxed_1612_ = lean_unbox(v_zeta_1596_);
v___y_99532__boxed_1613_ = lean_unbox(v___y_1597_);
v_usedOnly_boxed_1614_ = lean_unbox(v_usedOnly_1599_);
v___x_99533__boxed_1615_ = lean_unbox(v___x_1600_);
v___x_99534__boxed_1616_ = lean_unbox(v___x_1601_);
v_res_1617_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1594_, v_a_1595_, v_zeta_boxed_1612_, v___y_99532__boxed_1613_, v_x_1598_, v_usedOnly_boxed_1614_, v___x_99533__boxed_1615_, v___x_99534__boxed_1616_, v_snd_1602_, v_h_x27_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1618_, lean_object* v_a_1619_, uint8_t v_zeta_1620_, lean_object* v_x_1621_, uint8_t v_usedOnly_1622_, uint8_t v___x_1623_, lean_object* v_snd_1624_, uint8_t v___y_1625_, uint8_t v___x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1618_) == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1619_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
if (v_zeta_1620_ == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v_snd_1624_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_mk_empty_array_with_capacity(v___x_1637_);
v___x_1639_ = lean_array_push(v___x_1638_, v_x_1621_);
v___x_1640_ = 1;
v___x_1641_ = l_Lean_Meta_mkLetFVars(v___x_1639_, v_a_1636_, v_usedOnly_1622_, v___x_1623_, v___x_1640_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v___x_1639_);
return v___x_1641_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_a_1642_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_mk_empty_array_with_capacity(v___x_1643_);
v___x_1645_ = lean_array_push(v___x_1644_, v_x_1621_);
v___x_1646_ = l_Lean_Expr_abstractM(v_a_1642_, v___x_1645_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v___x_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_expr_instantiate1(v_a_1647_, v_snd_1624_);
lean_dec_ref(v_snd_1624_);
lean_dec(v_a_1647_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_dec_ref(v_snd_1624_);
return v___x_1646_;
}
}
}
else
{
lean_dec_ref(v_snd_1624_);
lean_dec_ref(v_x_1621_);
return v___x_1635_;
}
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1657_; 
v_val_1656_ = lean_ctor_get(v_eq_x3f_1618_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v_eq_x3f_1618_, 1);
lean_inc_ref(v_snd_1624_);
lean_inc_ref(v_x_1621_);
v___x_1657_ = l_Lean_Meta_mkEq(v_x_1621_, v_snd_1624_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
lean_inc_ref(v_x_1621_);
v___x_1659_ = l_Lean_Meta_mkEqRefl(v_x_1621_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = lean_box(v_zeta_1620_);
v___x_1662_ = lean_box(v___y_1625_);
v___x_1663_ = lean_box(v_usedOnly_1622_);
v___x_1664_ = lean_box(v___x_1623_);
v___x_1665_ = lean_box(v___x_1626_);
lean_inc(v_val_1656_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1666_, 0, v_val_1656_);
lean_closure_set(v___f_1666_, 1, v_a_1619_);
lean_closure_set(v___f_1666_, 2, v___x_1661_);
lean_closure_set(v___f_1666_, 3, v___x_1662_);
lean_closure_set(v___f_1666_, 4, v_x_1621_);
lean_closure_set(v___f_1666_, 5, v___x_1663_);
lean_closure_set(v___f_1666_, 6, v___x_1664_);
lean_closure_set(v___f_1666_, 7, v___x_1665_);
lean_closure_set(v___f_1666_, 8, v_snd_1624_);
v___x_1667_ = l_Lean_TSyntax_getId(v_val_1656_);
lean_dec(v_val_1656_);
v___x_1668_ = 0;
v___x_1669_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1667_, v_a_1658_, v_a_1660_, v___f_1666_, v___x_1626_, v___x_1668_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1669_;
}
else
{
lean_dec(v_a_1658_);
lean_dec(v_val_1656_);
lean_dec_ref(v_snd_1624_);
lean_dec_ref(v_x_1621_);
lean_dec_ref(v_a_1619_);
return v___x_1659_;
}
}
else
{
lean_dec(v_val_1656_);
lean_dec_ref(v_snd_1624_);
lean_dec_ref(v_x_1621_);
lean_dec_ref(v_a_1619_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_eq_x3f_1670_ = _args[0];
lean_object* v_a_1671_ = _args[1];
lean_object* v_zeta_1672_ = _args[2];
lean_object* v_x_1673_ = _args[3];
lean_object* v_usedOnly_1674_ = _args[4];
lean_object* v___x_1675_ = _args[5];
lean_object* v_snd_1676_ = _args[6];
lean_object* v___y_1677_ = _args[7];
lean_object* v___x_1678_ = _args[8];
lean_object* v___y_1679_ = _args[9];
lean_object* v___y_1680_ = _args[10];
lean_object* v___y_1681_ = _args[11];
lean_object* v___y_1682_ = _args[12];
lean_object* v___y_1683_ = _args[13];
lean_object* v___y_1684_ = _args[14];
lean_object* v___y_1685_ = _args[15];
lean_object* v___y_1686_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1687_; uint8_t v_usedOnly_boxed_1688_; uint8_t v___x_99687__boxed_1689_; uint8_t v___y_99689__boxed_1690_; uint8_t v___x_99690__boxed_1691_; lean_object* v_res_1692_; 
v_zeta_boxed_1687_ = lean_unbox(v_zeta_1672_);
v_usedOnly_boxed_1688_ = lean_unbox(v_usedOnly_1674_);
v___x_99687__boxed_1689_ = lean_unbox(v___x_1675_);
v___y_99689__boxed_1690_ = lean_unbox(v___y_1677_);
v___x_99690__boxed_1691_ = lean_unbox(v___x_1678_);
v_res_1692_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1670_, v_a_1671_, v_zeta_boxed_1687_, v_x_1673_, v_usedOnly_boxed_1688_, v___x_99687__boxed_1689_, v_snd_1676_, v___y_99689__boxed_1690_, v___x_99690__boxed_1691_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1693_, lean_object* v_eq_x3f_1694_, lean_object* v_a_1695_, uint8_t v_zeta_1696_, uint8_t v_usedOnly_1697_, uint8_t v___x_1698_, lean_object* v_snd_1699_, uint8_t v___y_1700_, uint8_t v___x_1701_, lean_object* v_letOrReassign_1702_, lean_object* v_a_1703_, lean_object* v_x_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
lean_inc_ref(v_x_1704_);
v___x_1713_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1693_, v_x_1704_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___y_1719_; lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1714_ = lean_box(v_zeta_1696_);
v___x_1715_ = lean_box(v_usedOnly_1697_);
v___x_1716_ = lean_box(v___x_1698_);
v___x_1717_ = lean_box(v___y_1700_);
v___x_1718_ = lean_box(v___x_1701_);
v___y_1719_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 17, 9);
lean_closure_set(v___y_1719_, 0, v_eq_x3f_1694_);
lean_closure_set(v___y_1719_, 1, v_a_1695_);
lean_closure_set(v___y_1719_, 2, v___x_1714_);
lean_closure_set(v___y_1719_, 3, v_x_1704_);
lean_closure_set(v___y_1719_, 4, v___x_1715_);
lean_closure_set(v___y_1719_, 5, v___x_1716_);
lean_closure_set(v___y_1719_, 6, v_snd_1699_);
lean_closure_set(v___y_1719_, 7, v___x_1717_);
lean_closure_set(v___y_1719_, 8, v___x_1718_);
v___x_1720_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1702_, v_a_1703_, v___y_1719_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1720_;
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_x_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_letOrReassign_1702_);
lean_dec_ref(v_snd_1699_);
lean_dec_ref(v_a_1695_);
lean_dec(v_eq_x3f_1694_);
v_a_1721_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1713_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1713_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1729_ = _args[0];
lean_object* v_eq_x3f_1730_ = _args[1];
lean_object* v_a_1731_ = _args[2];
lean_object* v_zeta_1732_ = _args[3];
lean_object* v_usedOnly_1733_ = _args[4];
lean_object* v___x_1734_ = _args[5];
lean_object* v_snd_1735_ = _args[6];
lean_object* v___y_1736_ = _args[7];
lean_object* v___x_1737_ = _args[8];
lean_object* v_letOrReassign_1738_ = _args[9];
lean_object* v_a_1739_ = _args[10];
lean_object* v_x_1740_ = _args[11];
lean_object* v___y_1741_ = _args[12];
lean_object* v___y_1742_ = _args[13];
lean_object* v___y_1743_ = _args[14];
lean_object* v___y_1744_ = _args[15];
lean_object* v___y_1745_ = _args[16];
lean_object* v___y_1746_ = _args[17];
lean_object* v___y_1747_ = _args[18];
lean_object* v___y_1748_ = _args[19];
_start:
{
uint8_t v_zeta_boxed_1749_; uint8_t v_usedOnly_boxed_1750_; uint8_t v___x_99800__boxed_1751_; uint8_t v___y_99802__boxed_1752_; uint8_t v___x_99803__boxed_1753_; lean_object* v_res_1754_; 
v_zeta_boxed_1749_ = lean_unbox(v_zeta_1732_);
v_usedOnly_boxed_1750_ = lean_unbox(v_usedOnly_1733_);
v___x_99800__boxed_1751_ = lean_unbox(v___x_1734_);
v___y_99802__boxed_1752_ = lean_unbox(v___y_1736_);
v___x_99803__boxed_1753_ = lean_unbox(v___x_1737_);
v_res_1754_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1729_, v_eq_x3f_1730_, v_a_1731_, v_zeta_boxed_1749_, v_usedOnly_boxed_1750_, v___x_99800__boxed_1751_, v_snd_1735_, v___y_99802__boxed_1752_, v___x_99803__boxed_1753_, v_letOrReassign_1738_, v_a_1739_, v_x_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1755_, lean_object* v_____do__lift_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1756_, v___x_1755_);
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1767_, lean_object* v_____do__lift_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
uint8_t v___x_99874__boxed_1777_; lean_object* v_res_1778_; 
v___x_99874__boxed_1777_ = lean_unbox(v___x_1767_);
v_res_1778_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99874__boxed_1777_, v_____do__lift_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v_____do__lift_1768_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1779_, lean_object* v___x_1780_, uint8_t v___x_1781_, lean_object* v___x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1779_, v___x_1780_, v___x_1781_, v___x_1781_, v___x_1782_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___x_99909__boxed_1804_; lean_object* v_res_1805_; 
v___x_99909__boxed_1804_ = lean_unbox(v___x_1794_);
v_res_1805_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1792_, v___x_1793_, v___x_99909__boxed_1804_, v___x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
lean_inc_ref(v___y_1807_);
v___x_1815_ = lean_apply_8(v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, lean_box(0));
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec_ref(v___y_1817_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1826_, lean_object* v_mkInfoTree_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v_a_1833_, lean_object* v_a_x3f_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v_infoState_1837_; lean_object* v_trees_1838_; lean_object* v___x_1839_; 
v___x_1836_ = lean_st_ref_get(v___y_1826_);
v_infoState_1837_ = lean_ctor_get(v___x_1836_, 7);
lean_inc_ref(v_infoState_1837_);
lean_dec(v___x_1836_);
v_trees_1838_ = lean_ctor_get(v_infoState_1837_, 2);
lean_inc_ref(v_trees_1838_);
lean_dec_ref(v_infoState_1837_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
v___x_1839_ = lean_apply_8(v_mkInfoTree_1827_, v_trees_1838_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1826_, lean_box(0));
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1878_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1878_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1878_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v_infoState_1845_; lean_object* v_env_1846_; lean_object* v_nextMacroScope_1847_; lean_object* v_ngen_1848_; lean_object* v_auxDeclNGen_1849_; lean_object* v_traceState_1850_; lean_object* v_cache_1851_; lean_object* v_messages_1852_; lean_object* v_snapshotTasks_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1877_; 
v___x_1844_ = lean_st_ref_take(v___y_1826_);
v_infoState_1845_ = lean_ctor_get(v___x_1844_, 7);
v_env_1846_ = lean_ctor_get(v___x_1844_, 0);
v_nextMacroScope_1847_ = lean_ctor_get(v___x_1844_, 1);
v_ngen_1848_ = lean_ctor_get(v___x_1844_, 2);
v_auxDeclNGen_1849_ = lean_ctor_get(v___x_1844_, 3);
v_traceState_1850_ = lean_ctor_get(v___x_1844_, 4);
v_cache_1851_ = lean_ctor_get(v___x_1844_, 5);
v_messages_1852_ = lean_ctor_get(v___x_1844_, 6);
v_snapshotTasks_1853_ = lean_ctor_get(v___x_1844_, 8);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1855_ = v___x_1844_;
v_isShared_1856_ = v_isSharedCheck_1877_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_snapshotTasks_1853_);
lean_inc(v_infoState_1845_);
lean_inc(v_messages_1852_);
lean_inc(v_cache_1851_);
lean_inc(v_traceState_1850_);
lean_inc(v_auxDeclNGen_1849_);
lean_inc(v_ngen_1848_);
lean_inc(v_nextMacroScope_1847_);
lean_inc(v_env_1846_);
lean_dec(v___x_1844_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1877_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint8_t v_enabled_1857_; lean_object* v_assignment_1858_; lean_object* v_lazyAssignment_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1875_; 
v_enabled_1857_ = lean_ctor_get_uint8(v_infoState_1845_, sizeof(void*)*3);
v_assignment_1858_ = lean_ctor_get(v_infoState_1845_, 0);
v_lazyAssignment_1859_ = lean_ctor_get(v_infoState_1845_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_infoState_1845_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_infoState_1845_, 2);
lean_dec(v_unused_1876_);
v___x_1861_ = v_infoState_1845_;
v_isShared_1862_ = v_isSharedCheck_1875_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_lazyAssignment_1859_);
lean_inc(v_assignment_1858_);
lean_dec(v_infoState_1845_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1875_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = l_Lean_PersistentArray_push___redArg(v_a_1833_, v_a_1840_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 2, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_assignment_1858_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_lazyAssignment_1859_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v___x_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*3, v_enabled_1857_);
v___x_1865_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 7, v___x_1865_);
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_env_1846_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_nextMacroScope_1847_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_ngen_1848_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_auxDeclNGen_1849_);
lean_ctor_set(v_reuseFailAlloc_1873_, 4, v_traceState_1850_);
lean_ctor_set(v_reuseFailAlloc_1873_, 5, v_cache_1851_);
lean_ctor_set(v_reuseFailAlloc_1873_, 6, v_messages_1852_);
lean_ctor_set(v_reuseFailAlloc_1873_, 7, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1873_, 8, v_snapshotTasks_1853_);
v___x_1867_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1868_ = lean_st_ref_put(v___y_1826_, v___x_1867_);
v___x_1869_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1869_);
v___x_1871_ = v___x_1842_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_a_1833_);
v_a_1879_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1839_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1839_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_1887_, lean_object* v_mkInfoTree_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v_a_1894_, lean_object* v_a_x3f_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1887_, v_mkInfoTree_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v_a_1894_, v_a_x3f_1895_);
lean_dec(v_a_x3f_1895_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1887_);
return v_res_1897_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_unsigned_to_nat(32u);
v___x_1899_ = lean_mk_empty_array_with_capacity(v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1901_ = ((size_t)5ULL);
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_unsigned_to_nat(32u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_1906_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
lean_ctor_set(v___x_1906_, 2, v___x_1902_);
lean_ctor_set(v___x_1906_, 3, v___x_1902_);
lean_ctor_set_usize(v___x_1906_, 4, v___x_1901_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_infoState_1910_; lean_object* v_trees_1911_; lean_object* v___x_1912_; lean_object* v_infoState_1913_; lean_object* v_env_1914_; lean_object* v_nextMacroScope_1915_; lean_object* v_ngen_1916_; lean_object* v_auxDeclNGen_1917_; lean_object* v_traceState_1918_; lean_object* v_cache_1919_; lean_object* v_messages_1920_; lean_object* v_snapshotTasks_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1942_; 
v___x_1909_ = lean_st_ref_get(v___y_1907_);
v_infoState_1910_ = lean_ctor_get(v___x_1909_, 7);
lean_inc_ref(v_infoState_1910_);
lean_dec(v___x_1909_);
v_trees_1911_ = lean_ctor_get(v_infoState_1910_, 2);
lean_inc_ref(v_trees_1911_);
lean_dec_ref(v_infoState_1910_);
v___x_1912_ = lean_st_ref_take(v___y_1907_);
v_infoState_1913_ = lean_ctor_get(v___x_1912_, 7);
v_env_1914_ = lean_ctor_get(v___x_1912_, 0);
v_nextMacroScope_1915_ = lean_ctor_get(v___x_1912_, 1);
v_ngen_1916_ = lean_ctor_get(v___x_1912_, 2);
v_auxDeclNGen_1917_ = lean_ctor_get(v___x_1912_, 3);
v_traceState_1918_ = lean_ctor_get(v___x_1912_, 4);
v_cache_1919_ = lean_ctor_get(v___x_1912_, 5);
v_messages_1920_ = lean_ctor_get(v___x_1912_, 6);
v_snapshotTasks_1921_ = lean_ctor_get(v___x_1912_, 8);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1923_ = v___x_1912_;
v_isShared_1924_ = v_isSharedCheck_1942_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snapshotTasks_1921_);
lean_inc(v_infoState_1913_);
lean_inc(v_messages_1920_);
lean_inc(v_cache_1919_);
lean_inc(v_traceState_1918_);
lean_inc(v_auxDeclNGen_1917_);
lean_inc(v_ngen_1916_);
lean_inc(v_nextMacroScope_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1912_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1942_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint8_t v_enabled_1925_; lean_object* v_assignment_1926_; lean_object* v_lazyAssignment_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1940_; 
v_enabled_1925_ = lean_ctor_get_uint8(v_infoState_1913_, sizeof(void*)*3);
v_assignment_1926_ = lean_ctor_get(v_infoState_1913_, 0);
v_lazyAssignment_1927_ = lean_ctor_get(v_infoState_1913_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_infoState_1913_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_infoState_1913_, 2);
lean_dec(v_unused_1941_);
v___x_1929_ = v_infoState_1913_;
v_isShared_1930_ = v_isSharedCheck_1940_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_lazyAssignment_1927_);
lean_inc(v_assignment_1926_);
lean_dec(v_infoState_1913_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1940_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 2, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_assignment_1926_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_lazyAssignment_1927_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v___x_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1939_, sizeof(void*)*3, v_enabled_1925_);
v___x_1933_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 7, v___x_1933_);
v___x_1935_ = v___x_1923_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_env_1914_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_nextMacroScope_1915_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_ngen_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_auxDeclNGen_1917_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_traceState_1918_);
lean_ctor_set(v_reuseFailAlloc_1938_, 5, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1938_, 6, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_1938_, 7, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1938_, 8, v_snapshotTasks_1921_);
v___x_1935_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_st_ref_put(v___y_1907_, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_trees_1911_);
return v___x_1937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1943_);
lean_dec(v___y_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_1946_, lean_object* v_mkInfoTree_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v_infoState_1956_; uint8_t v_enabled_1957_; 
v___x_1955_ = lean_st_ref_get(v___y_1953_);
v_infoState_1956_ = lean_ctor_get(v___x_1955_, 7);
lean_inc_ref(v_infoState_1956_);
lean_dec(v___x_1955_);
v_enabled_1957_ = lean_ctor_get_uint8(v_infoState_1956_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1956_);
if (v_enabled_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref(v_mkInfoTree_1947_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
v___x_1958_ = lean_apply_7(v_x_1946_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v_r_1961_; 
v___x_1959_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1953_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
v_r_1961_ = lean_apply_7(v_x_1946_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
if (lean_obj_tag(v_r_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1986_; 
v_a_1962_ = lean_ctor_get(v_r_1961_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_r_1961_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1964_ = v_r_1961_;
v_isShared_1965_ = v_isSharedCheck_1986_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v_r_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1986_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
lean_inc(v_a_1962_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 1);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1953_, v_mkInfoTree_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v_a_1960_, v___x_1967_);
lean_dec_ref(v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1976_);
v___x_1970_ = v___x_1968_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v___x_1968_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_a_1962_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1962_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_a_1962_);
v_a_1977_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1968_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1968_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_a_1987_ = lean_ctor_get(v_r_1961_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v_r_1961_, 1);
v___x_1988_ = lean_box(0);
v___x_1989_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1953_, v_mkInfoTree_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v_a_1960_, v___x_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1989_, 0);
lean_dec(v_unused_1997_);
v___x_1991_ = v___x_1989_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v___x_1989_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 1);
lean_ctor_set(v___x_1991_, 0, v_a_1987_);
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1987_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1987_);
v_a_1998_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1989_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1989_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_2006_, lean_object* v_mkInfoTree_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2006_, v_mkInfoTree_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2016_, lean_object* v_output_2017_, lean_object* v_trees_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_lctx_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_lctx_2026_ = lean_ctor_get(v___y_2021_, 2);
lean_inc_ref(v_lctx_2026_);
v___x_2027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2027_, 0, v_lctx_2026_);
lean_ctor_set(v___x_2027_, 1, v_stx_2016_);
lean_ctor_set(v___x_2027_, 2, v_output_2017_);
v___x_2028_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v_trees_2018_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2031_, lean_object* v_output_2032_, lean_object* v_trees_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2031_, v_output_2032_, v_trees_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2042_, lean_object* v_output_2043_, lean_object* v_x_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___f_2052_; lean_object* v___x_2053_; 
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2052_, 0, v_stx_2042_);
lean_closure_set(v___f_2052_, 1, v_output_2043_);
v___x_2053_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2044_, v___f_2052_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2054_, lean_object* v_output_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2054_, v_output_2055_, v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2065_, lean_object* v_afterStx_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___f_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc_ref(v___y_2068_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2076_, 0, v_x_2067_);
lean_closure_set(v___f_2076_, 1, v___y_2068_);
lean_inc(v_afterStx_2066_);
lean_inc(v_beforeStx_2065_);
v___x_2077_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2077_, 0, lean_box(0));
lean_closure_set(v___x_2077_, 1, v_beforeStx_2065_);
lean_closure_set(v___x_2077_, 2, v_afterStx_2066_);
lean_closure_set(v___x_2077_, 3, v___f_2076_);
v___x_2078_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2065_, v_afterStx_2066_, v___x_2077_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2078_) == 0)
{
return v___x_2078_;
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2087_, lean_object* v_afterStx_2088_, lean_object* v_x_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2087_, v_afterStx_2088_, v_x_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2098_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2102_ = l_String_toRawSubstring_x27(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2124_, uint8_t v___x_2125_, lean_object* v_config_2126_, lean_object* v_a_2127_, uint8_t v___x_2128_, lean_object* v___x_2129_, lean_object* v___x_2130_, lean_object* v___x_2131_, lean_object* v___f_2132_, lean_object* v___x_2133_, lean_object* v_body_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_term_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v_ref_2151_; lean_object* v___y_2152_; lean_object* v_ref_2158_; lean_object* v_quotContext_2159_; lean_object* v_currMacroScope_2160_; lean_object* v_ref_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v_eq_x3f_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_ref_2158_ = lean_ctor_get(v___y_2140_, 5);
v_quotContext_2159_ = lean_ctor_get(v___y_2140_, 10);
v_currMacroScope_2160_ = lean_ctor_get(v___y_2140_, 11);
v_ref_2161_ = l_Lean_replaceRef(v_rhs_2124_, v_ref_2158_);
v___x_2162_ = l_Lean_SourceInfo_fromRef(v_ref_2161_, v___x_2125_);
lean_dec(v_ref_2161_);
v___x_2163_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2162_, 2);
v___x_2164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2166_ = lean_ctor_get(v_config_2126_, 0);
lean_inc(v_eq_x3f_2166_);
lean_dec_ref(v_config_2126_);
v___x_2167_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2160_);
lean_inc(v_quotContext_2159_);
v___x_2168_ = l_Lean_addMacroScope(v_quotContext_2159_, v___x_2167_, v_currMacroScope_2160_);
v___x_2169_ = lean_box(0);
lean_inc(v___x_2168_);
v___x_2170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2162_);
lean_ctor_set(v___x_2170_, 1, v___x_2165_);
lean_ctor_set(v___x_2170_, 2, v___x_2168_);
lean_ctor_set(v___x_2170_, 3, v___x_2169_);
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2131_);
lean_inc_ref(v___x_2130_);
lean_inc_ref(v___x_2129_);
v___x_2172_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2171_);
v___x_2173_ = l_Lean_Syntax_node2(v___x_2162_, v___x_2172_, v___x_2164_, v___x_2170_);
if (lean_obj_tag(v_eq_x3f_2166_) == 1)
{
lean_object* v_val_2174_; lean_object* v___x_2175_; 
v_val_2174_ = lean_ctor_get(v_eq_x3f_2166_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_eq_x3f_2166_, 1);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v_ref_2158_);
v___x_2175_ = lean_apply_9(v___f_2132_, v_ref_2158_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_n(v_a_2176_, 23);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2131_, 5);
lean_inc_ref_n(v___x_2130_, 5);
lean_inc_ref_n(v___x_2129_, 5);
v___x_2178_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2177_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2176_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2181_, 0, v_a_2176_);
lean_ctor_set(v___x_2181_, 1, v___x_2163_);
v___x_2182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2176_);
lean_ctor_set(v___x_2182_, 1, v___x_2165_);
lean_ctor_set(v___x_2182_, 2, v___x_2168_);
lean_ctor_set(v___x_2182_, 3, v___x_2169_);
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_a_2176_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2176_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2188_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2176_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2192_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2176_);
lean_ctor_set(v___x_2193_, 1, v___x_2191_);
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2195_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2176_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
v___x_2197_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2198_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2197_);
v___x_2199_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2176_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_Lean_Syntax_node2(v_a_2176_, v___x_2194_, v_val_2174_, v___x_2200_);
v___x_2202_ = l_Lean_Syntax_node2(v_a_2176_, v___x_2198_, v___x_2201_, v___x_2173_);
v___x_2203_ = l_Lean_Syntax_node1(v_a_2176_, v___x_2194_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_a_2176_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2207_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2209_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2208_);
v___x_2210_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_a_2176_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Lean_Syntax_node1(v_a_2176_, v___x_2194_, v___x_2133_);
v___x_2213_ = l_Lean_Syntax_node1(v_a_2176_, v___x_2194_, v___x_2212_);
v___x_2214_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_a_2176_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_Syntax_node4(v_a_2176_, v___x_2209_, v___x_2211_, v___x_2213_, v___x_2215_, v_body_2134_);
v___x_2217_ = l_Lean_Syntax_node1(v_a_2176_, v___x_2194_, v___x_2216_);
v___x_2218_ = l_Lean_Syntax_node1(v_a_2176_, v___x_2207_, v___x_2217_);
lean_inc_ref(v___x_2196_);
v___x_2219_ = l_Lean_Syntax_node6(v_a_2176_, v___x_2192_, v___x_2193_, v___x_2196_, v___x_2196_, v___x_2203_, v___x_2205_, v___x_2218_);
lean_inc_ref(v___x_2186_);
lean_inc_ref(v___x_2182_);
lean_inc_ref(v___x_2181_);
v___x_2220_ = l_Lean_Syntax_node5(v_a_2176_, v___x_2188_, v___x_2190_, v___x_2181_, v___x_2182_, v___x_2186_, v___x_2219_);
v___x_2221_ = l_Lean_Syntax_node7(v_a_2176_, v___x_2178_, v___x_2180_, v___x_2181_, v___x_2182_, v___x_2184_, v_rhs_2124_, v___x_2186_, v___x_2220_);
lean_inc(v_ref_2158_);
v_term_2144_ = v___x_2221_;
v___y_2145_ = v___y_2135_;
v___y_2146_ = v___y_2136_;
v___y_2147_ = v___y_2137_;
v___y_2148_ = v___y_2138_;
v___y_2149_ = v___y_2139_;
v___y_2150_ = v___y_2140_;
v_ref_2151_ = v_ref_2158_;
v___y_2152_ = v___y_2141_;
goto v___jp_2143_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_val_2174_);
lean_dec(v___x_2173_);
lean_dec(v___x_2168_);
lean_dec(v_body_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v___x_2129_);
lean_dec_ref(v_a_2127_);
lean_dec(v_rhs_2124_);
v_a_2222_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2175_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2175_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v___x_2230_; 
lean_dec(v_eq_x3f_2166_);
lean_inc_ref(v_a_2127_);
v___x_2230_ = l_Lean_Elab_Term_exprToSyntax(v_a_2127_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v_ref_2158_);
v___x_2232_ = lean_apply_9(v___f_2132_, v_ref_2158_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, lean_box(0));
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_n(v_a_2233_, 32);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2131_, 8);
lean_inc_ref_n(v___x_2130_, 8);
lean_inc_ref_n(v___x_2129_, 8);
v___x_2235_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2234_);
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_a_2233_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2233_);
lean_ctor_set(v___x_2238_, 1, v___x_2163_);
v___x_2239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2233_);
lean_ctor_set(v___x_2239_, 1, v___x_2165_);
lean_ctor_set(v___x_2239_, 2, v___x_2168_);
lean_ctor_set(v___x_2239_, 3, v___x_2169_);
v___x_2240_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2233_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_a_2233_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2245_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2244_);
v___x_2246_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2233_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2249_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2233_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
v___x_2251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2252_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2253_, 0, v_a_2233_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
lean_ctor_set(v___x_2253_, 2, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2255_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2254_);
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_a_2233_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_a_2233_);
lean_ctor_set(v___x_2258_, 1, v___x_2254_);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2260_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2259_);
v___x_2261_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_a_2233_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2264_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_a_2233_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2264_, v___x_2266_);
v___x_2268_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2267_);
v___x_2269_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_a_2233_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
lean_inc_ref_n(v___x_2253_, 2);
v___x_2271_ = l_Lean_Syntax_node5(v_a_2233_, v___x_2260_, v___x_2262_, v___x_2268_, v___x_2253_, v___x_2270_, v_a_2231_);
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2233_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
lean_inc_ref(v___x_2241_);
v___x_2274_ = l_Lean_Syntax_node5(v_a_2233_, v___x_2255_, v___x_2257_, v___x_2258_, v___x_2241_, v___x_2271_, v___x_2273_);
v___x_2275_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2277_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_node2(v_a_2233_, v___x_2277_, v___x_2253_, v___x_2173_);
v___x_2279_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2233_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2283_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2285_ = l_Lean_Name_mkStr4(v___x_2129_, v___x_2130_, v___x_2131_, v___x_2284_);
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_a_2233_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2133_);
v___x_2289_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2288_);
v___x_2290_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_a_2233_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_Syntax_node4(v_a_2233_, v___x_2285_, v___x_2287_, v___x_2289_, v___x_2291_, v_body_2134_);
v___x_2293_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2251_, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node1(v_a_2233_, v___x_2283_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node6(v_a_2233_, v___x_2249_, v___x_2250_, v___x_2253_, v___x_2275_, v___x_2279_, v___x_2281_, v___x_2294_);
lean_inc_ref(v___x_2243_);
lean_inc_ref(v___x_2239_);
lean_inc_ref(v___x_2238_);
v___x_2296_ = l_Lean_Syntax_node5(v_a_2233_, v___x_2245_, v___x_2247_, v___x_2238_, v___x_2239_, v___x_2243_, v___x_2295_);
v___x_2297_ = l_Lean_Syntax_node7(v_a_2233_, v___x_2235_, v___x_2237_, v___x_2238_, v___x_2239_, v___x_2241_, v_rhs_2124_, v___x_2243_, v___x_2296_);
lean_inc(v_ref_2158_);
v_term_2144_ = v___x_2297_;
v___y_2145_ = v___y_2135_;
v___y_2146_ = v___y_2136_;
v___y_2147_ = v___y_2137_;
v___y_2148_ = v___y_2138_;
v___y_2149_ = v___y_2139_;
v___y_2150_ = v___y_2140_;
v_ref_2151_ = v_ref_2158_;
v___y_2152_ = v___y_2141_;
goto v___jp_2143_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_a_2231_);
lean_dec(v___x_2173_);
lean_dec(v___x_2168_);
lean_dec(v_body_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v___x_2129_);
lean_dec_ref(v_a_2127_);
lean_dec(v_rhs_2124_);
v_a_2298_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2232_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2232_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v___x_2173_);
lean_dec(v___x_2168_);
lean_dec(v_body_2134_);
lean_dec(v___x_2133_);
lean_dec_ref(v___f_2132_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v___x_2129_);
lean_dec_ref(v_a_2127_);
lean_dec(v_rhs_2124_);
v_a_2306_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2230_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2230_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
v___jp_2143_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2127_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_box(v___x_2128_);
lean_inc(v_term_2144_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2156_, 0, v_term_2144_);
lean_closure_set(v___f_2156_, 1, v___x_2153_);
lean_closure_set(v___f_2156_, 2, v___x_2155_);
lean_closure_set(v___f_2156_, 3, v___x_2154_);
v___x_2157_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2151_, v_term_2144_, v___f_2156_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2152_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2314_ = _args[0];
lean_object* v___x_2315_ = _args[1];
lean_object* v_config_2316_ = _args[2];
lean_object* v_a_2317_ = _args[3];
lean_object* v___x_2318_ = _args[4];
lean_object* v___x_2319_ = _args[5];
lean_object* v___x_2320_ = _args[6];
lean_object* v___x_2321_ = _args[7];
lean_object* v___f_2322_ = _args[8];
lean_object* v___x_2323_ = _args[9];
lean_object* v_body_2324_ = _args[10];
lean_object* v___y_2325_ = _args[11];
lean_object* v___y_2326_ = _args[12];
lean_object* v___y_2327_ = _args[13];
lean_object* v___y_2328_ = _args[14];
lean_object* v___y_2329_ = _args[15];
lean_object* v___y_2330_ = _args[16];
lean_object* v___y_2331_ = _args[17];
lean_object* v___y_2332_ = _args[18];
_start:
{
uint8_t v___x_100438__boxed_2333_; uint8_t v___x_100440__boxed_2334_; lean_object* v_res_2335_; 
v___x_100438__boxed_2333_ = lean_unbox(v___x_2315_);
v___x_100440__boxed_2334_ = lean_unbox(v___x_2318_);
v_res_2335_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2314_, v___x_100438__boxed_2333_, v_config_2316_, v_a_2317_, v___x_100440__boxed_2334_, v___x_2319_, v___x_2320_, v___x_2321_, v___f_2322_, v___x_2323_, v_body_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2336_, lean_object* v___y_2337_){
_start:
{
if (lean_obj_tag(v_x_2336_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_a_2338_);
v___x_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_a_2338_);
lean_ctor_set(v___x_2339_, 1, v___y_2337_);
return v___x_2339_;
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v_x_2336_, 0);
lean_inc(v_a_2340_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_a_2340_);
lean_ctor_set(v___x_2341_, 1, v___y_2337_);
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2342_, v___y_2343_);
lean_dec_ref(v_x_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2345_, lean_object* v_stx_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2345_, v_stx_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
if (lean_obj_tag(v_a_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
v_a_2351_ = lean_ctor_get(v___x_2349_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v___x_2349_, 0);
lean_dec(v_unused_2360_);
v___x_2353_ = v___x_2349_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2355_);
v___x_2357_ = v___x_2353_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2351_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2389_; 
v_val_2361_ = lean_ctor_get(v_a_2350_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2350_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2363_ = v_a_2350_;
v_isShared_2364_ = v_isSharedCheck_2389_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_dec(v_a_2350_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2389_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_snd_2365_; 
v_snd_2365_ = lean_ctor_get(v_val_2361_, 1);
lean_inc(v_snd_2365_);
lean_dec(v_val_2361_);
if (lean_obj_tag(v_snd_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2375_; 
lean_del_object(v___x_2363_);
v_a_2366_ = lean_ctor_get(v___x_2349_, 1);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2349_, 2);
v_a_2367_ = lean_ctor_get(v_snd_2365_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_snd_2365_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2369_ = v_snd_2365_;
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v_snd_2365_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2372_, v_a_2366_);
lean_dec_ref(v___x_2372_);
return v___x_2373_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2388_; 
v_a_2376_ = lean_ctor_get(v___x_2349_, 1);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2349_, 2);
v_a_2377_ = lean_ctor_get(v_snd_2365_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_snd_2365_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2379_ = v_snd_2365_;
v_isShared_2380_ = v_isSharedCheck_2388_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v_snd_2365_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2388_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v_a_2377_);
v___x_2382_ = v___x_2363_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2382_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2384_, v_a_2376_);
lean_dec_ref(v___x_2384_);
return v___x_2385_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_a_2390_ = lean_ctor_get(v___x_2349_, 0);
v_a_2391_ = lean_ctor_get(v___x_2349_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2349_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_inc(v_a_2390_);
lean_dec(v___x_2349_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2399_, lean_object* v_stx_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2399_, v_stx_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_currNamespace_2404_);
lean_ctor_set(v___x_2407_, 1, v___y_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2408_, v___y_2409_, v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2412_, lean_object* v_declName_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v___x_2416_; lean_object* v_env_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2416_ = 0;
v_env_2417_ = l_Lean_Environment_setExporting(v_env_2412_, v___x_2416_);
lean_inc(v_declName_2413_);
v___x_2418_ = l_Lean_mkPrivateName(v_env_2417_, v_declName_2413_);
v___x_2419_ = 1;
lean_inc_ref(v_env_2417_);
v___x_2420_ = l_Lean_Environment_contains(v_env_2417_, v___x_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = l_Lean_privateToUserName(v_declName_2413_);
v___x_2422_ = l_Lean_Environment_contains(v_env_2417_, v___x_2421_, v___x_2419_);
v___x_2423_ = lean_box(v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___y_2415_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v_env_2417_);
lean_dec(v_declName_2413_);
v___x_2425_ = lean_box(v___x_2420_);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___y_2415_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2427_, lean_object* v_declName_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2427_, v_declName_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2432_, lean_object* v_currNamespace_2433_, lean_object* v_openDecls_2434_, lean_object* v_n_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = l_Lean_ResolveName_resolveNamespace(v_env_2432_, v_currNamespace_2433_, v_openDecls_2434_, v_n_2435_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___y_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2440_, lean_object* v_currNamespace_2441_, lean_object* v_openDecls_2442_, lean_object* v_n_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2440_, v_currNamespace_2441_, v_openDecls_2442_, v_n_2443_, v___y_2444_, v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2447_, lean_object* v_options_2448_, lean_object* v_currNamespace_2449_, lean_object* v_openDecls_2450_, lean_object* v_n_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = l_Lean_ResolveName_resolveGlobalName(v_env_2447_, v_options_2448_, v_currNamespace_2449_, v_openDecls_2450_, v_n_2451_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2456_, lean_object* v_options_2457_, lean_object* v_currNamespace_2458_, lean_object* v_openDecls_2459_, lean_object* v_n_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2456_, v_options_2457_, v_currNamespace_2458_, v_openDecls_2459_, v_n_2460_, v___y_2461_, v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_options_2457_);
return v_res_2463_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2464_, lean_object* v_i_2465_, lean_object* v_k_2466_){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = lean_array_get_size(v_keys_2464_);
v___x_2468_ = lean_nat_dec_lt(v_i_2465_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_dec(v_i_2465_);
return v___x_2468_;
}
else
{
lean_object* v_k_x27_2469_; uint8_t v___x_2470_; 
v_k_x27_2469_ = lean_array_fget_borrowed(v_keys_2464_, v_i_2465_);
v___x_2470_ = l_Lean_instBEqExtraModUse_beq(v_k_2466_, v_k_x27_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = lean_nat_add(v_i_2465_, v___x_2471_);
lean_dec(v_i_2465_);
v_i_2465_ = v___x_2472_;
goto _start;
}
else
{
lean_dec(v_i_2465_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2474_, lean_object* v_i_2475_, lean_object* v_k_2476_){
_start:
{
uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_res_2477_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2474_, v_i_2475_, v_k_2476_);
lean_dec_ref(v_k_2476_);
lean_dec_ref(v_keys_2474_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2479_, size_t v_x_2480_, lean_object* v_x_2481_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_object* v_es_2482_; lean_object* v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; lean_object* v_j_2486_; lean_object* v___x_2487_; 
v_es_2482_ = lean_ctor_get(v_x_2479_, 0);
v___x_2483_ = lean_box(2);
v___x_2484_ = ((size_t)31ULL);
v___x_2485_ = lean_usize_land(v_x_2480_, v___x_2484_);
v_j_2486_ = lean_usize_to_nat(v___x_2485_);
v___x_2487_ = lean_array_get_borrowed(v___x_2483_, v_es_2482_, v_j_2486_);
lean_dec(v_j_2486_);
switch(lean_obj_tag(v___x_2487_))
{
case 0:
{
lean_object* v_key_2488_; uint8_t v___x_2489_; 
v_key_2488_ = lean_ctor_get(v___x_2487_, 0);
v___x_2489_ = l_Lean_instBEqExtraModUse_beq(v_x_2481_, v_key_2488_);
return v___x_2489_;
}
case 1:
{
lean_object* v_node_2490_; size_t v___x_2491_; size_t v___x_2492_; 
v_node_2490_ = lean_ctor_get(v___x_2487_, 0);
v___x_2491_ = ((size_t)5ULL);
v___x_2492_ = lean_usize_shift_right(v_x_2480_, v___x_2491_);
v_x_2479_ = v_node_2490_;
v_x_2480_ = v___x_2492_;
goto _start;
}
default: 
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
}
}
else
{
lean_object* v_ks_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_ks_2495_ = lean_ctor_get(v_x_2479_, 0);
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2495_, v___x_2496_, v_x_2481_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
size_t v_x_101026__boxed_2501_; uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_x_101026__boxed_2501_ = lean_unbox_usize(v_x_2499_);
lean_dec(v_x_2499_);
v_res_2502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2498_, v_x_101026__boxed_2501_, v_x_2500_);
lean_dec_ref(v_x_2500_);
lean_dec_ref(v_x_2498_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2504_, lean_object* v_x_2505_){
_start:
{
uint64_t v___x_2506_; size_t v___x_2507_; uint8_t v___x_2508_; 
v___x_2506_ = l_Lean_instHashableExtraModUse_hash(v_x_2505_);
v___x_2507_ = lean_uint64_to_usize(v___x_2506_);
v___x_2508_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2504_, v___x_2507_, v_x_2505_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2509_, v_x_2510_);
lean_dec_ref(v_x_2510_);
lean_dec_ref(v_x_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2513_; double v___x_2514_; 
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = lean_float_of_nat(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2517_, lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_ref_2524_; lean_object* v___x_2525_; lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2570_; 
v_ref_2524_ = lean_ctor_get(v___y_2521_, 5);
v___x_2525_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2570_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2570_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v_traceState_2531_; lean_object* v_env_2532_; lean_object* v_nextMacroScope_2533_; lean_object* v_ngen_2534_; lean_object* v_auxDeclNGen_2535_; lean_object* v_cache_2536_; lean_object* v_messages_2537_; lean_object* v_infoState_2538_; lean_object* v_snapshotTasks_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2569_; 
v___x_2530_ = lean_st_ref_take(v___y_2522_);
v_traceState_2531_ = lean_ctor_get(v___x_2530_, 4);
v_env_2532_ = lean_ctor_get(v___x_2530_, 0);
v_nextMacroScope_2533_ = lean_ctor_get(v___x_2530_, 1);
v_ngen_2534_ = lean_ctor_get(v___x_2530_, 2);
v_auxDeclNGen_2535_ = lean_ctor_get(v___x_2530_, 3);
v_cache_2536_ = lean_ctor_get(v___x_2530_, 5);
v_messages_2537_ = lean_ctor_get(v___x_2530_, 6);
v_infoState_2538_ = lean_ctor_get(v___x_2530_, 7);
v_snapshotTasks_2539_ = lean_ctor_get(v___x_2530_, 8);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2541_ = v___x_2530_;
v_isShared_2542_ = v_isSharedCheck_2569_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_snapshotTasks_2539_);
lean_inc(v_infoState_2538_);
lean_inc(v_messages_2537_);
lean_inc(v_cache_2536_);
lean_inc(v_traceState_2531_);
lean_inc(v_auxDeclNGen_2535_);
lean_inc(v_ngen_2534_);
lean_inc(v_nextMacroScope_2533_);
lean_inc(v_env_2532_);
lean_dec(v___x_2530_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2569_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
uint64_t v_tid_2543_; lean_object* v_traces_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2568_; 
v_tid_2543_ = lean_ctor_get_uint64(v_traceState_2531_, sizeof(void*)*1);
v_traces_2544_ = lean_ctor_get(v_traceState_2531_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_traceState_2531_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2546_ = v_traceState_2531_;
v_isShared_2547_ = v_isSharedCheck_2568_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_traces_2544_);
lean_dec(v_traceState_2531_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2568_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; double v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2548_ = lean_box(0);
v___x_2549_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2550_ = 0;
v___x_2551_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2552_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2552_, 0, v_cls_2517_);
lean_ctor_set(v___x_2552_, 1, v___x_2548_);
lean_ctor_set(v___x_2552_, 2, v___x_2551_);
lean_ctor_set_float(v___x_2552_, sizeof(void*)*3, v___x_2549_);
lean_ctor_set_float(v___x_2552_, sizeof(void*)*3 + 8, v___x_2549_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*3 + 16, v___x_2550_);
v___x_2553_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2554_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v_a_2526_);
lean_ctor_set(v___x_2554_, 2, v___x_2553_);
lean_inc(v_ref_2524_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_ref_2524_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_PersistentArray_push___redArg(v_traces_2544_, v___x_2555_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2556_);
v___x_2558_ = v___x_2546_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2556_);
lean_ctor_set_uint64(v_reuseFailAlloc_2567_, sizeof(void*)*1, v_tid_2543_);
v___x_2558_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 4, v___x_2558_);
v___x_2560_ = v___x_2541_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_env_2532_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_nextMacroScope_2533_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_ngen_2534_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_auxDeclNGen_2535_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2566_, 5, v_cache_2536_);
lean_ctor_set(v_reuseFailAlloc_2566_, 6, v_messages_2537_);
lean_ctor_set(v_reuseFailAlloc_2566_, 7, v_infoState_2538_);
lean_ctor_set(v_reuseFailAlloc_2566_, 8, v_snapshotTasks_2539_);
v___x_2560_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2561_ = lean_st_ref_put(v___y_2522_, v___x_2560_);
v___x_2562_ = lean_box(0);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2562_);
v___x_2564_ = v___x_2528_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2571_, lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2571_, v_msg_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
return v_res_2578_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2582_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2583_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2582_, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2584_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
return v___x_2588_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2590_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
lean_ctor_set(v___x_2590_, 3, v___x_2589_);
lean_ctor_set(v___x_2590_, 4, v___x_2589_);
lean_ctor_set(v___x_2590_, 5, v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2596_ = l_Lean_stringToMessageData(v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2601_ = l_Lean_stringToMessageData(v___x_2600_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v_cls_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_cls_2605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2607_ = l_Lean_Name_append(v___x_2606_, v_cls_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2610_ = l_Lean_stringToMessageData(v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2618_, uint8_t v_isMeta_2619_, lean_object* v_hint_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; lean_object* v_env_2630_; uint8_t v_isExporting_2631_; lean_object* v___x_2632_; lean_object* v_env_2633_; lean_object* v___x_2634_; lean_object* v_entry_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2629_ = lean_st_ref_get(v___y_2627_);
v_env_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_ref(v_env_2630_);
lean_dec(v___x_2629_);
v_isExporting_2631_ = lean_ctor_get_uint8(v_env_2630_, sizeof(void*)*8);
lean_dec_ref(v_env_2630_);
v___x_2632_ = lean_st_ref_get(v___y_2627_);
v_env_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_ref(v_env_2633_);
lean_dec(v___x_2632_);
v___x_2634_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2618_);
v_entry_2635_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2635_, 0, v_mod_2618_);
lean_ctor_set_uint8(v_entry_2635_, sizeof(void*)*1, v_isExporting_2631_);
lean_ctor_set_uint8(v_entry_2635_, sizeof(void*)*1 + 1, v_isMeta_2619_);
v___x_2636_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2637_ = lean_box(1);
v___x_2638_ = lean_box(0);
v___x_2681_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2634_, v___x_2636_, v_env_2633_, v___x_2637_, v___x_2638_);
v___x_2682_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2681_, v_entry_2635_);
lean_dec(v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v_options_2683_; uint8_t v_hasTrace_2684_; 
v_options_2683_ = lean_ctor_get(v___y_2626_, 2);
v_hasTrace_2684_ = lean_ctor_get_uint8(v_options_2683_, sizeof(void*)*1);
if (v_hasTrace_2684_ == 0)
{
lean_dec(v_hint_2620_);
lean_dec(v_mod_2618_);
v___y_2640_ = v___y_2625_;
v___y_2641_ = v___y_2627_;
goto v___jp_2639_;
}
else
{
lean_object* v_inheritedTraceOptions_2685_; lean_object* v_cls_2686_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_inheritedTraceOptions_2685_ = lean_ctor_get(v___y_2626_, 13);
v_cls_2686_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2706_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
v___x_2707_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2685_, v_options_2683_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_dec(v_hint_2620_);
lean_dec(v_mod_2618_);
v___y_2640_ = v___y_2625_;
v___y_2641_ = v___y_2627_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2708_; lean_object* v___y_2710_; 
v___x_2708_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
if (v_isExporting_2631_ == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__23));
v___y_2710_ = v___x_2717_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2718_; 
v___x_2718_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__24));
v___y_2710_ = v___x_2718_;
goto v___jp_2709_;
}
v___jp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_inc_ref(v___y_2710_);
v___x_2711_ = l_Lean_stringToMessageData(v___y_2710_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2708_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
if (v_isMeta_2619_ == 0)
{
lean_object* v___x_2715_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2693_ = v___x_2714_;
v___y_2694_ = v___x_2715_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2716_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2693_ = v___x_2714_;
v___y_2694_ = v___x_2716_;
goto v___jp_2692_;
}
}
}
v___jp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___y_2688_);
lean_ctor_set(v___x_2690_, 1, v___y_2689_);
v___x_2691_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2686_, v___x_2690_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_dec_ref_known(v___x_2691_, 1);
v___y_2640_ = v___y_2625_;
v___y_2641_ = v___y_2627_;
goto v___jp_2639_;
}
else
{
lean_dec_ref_known(v_entry_2635_, 1);
return v___x_2691_;
}
}
v___jp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
lean_inc_ref(v___y_2694_);
v___x_2695_ = l_Lean_stringToMessageData(v___y_2694_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___y_2693_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_MessageData_ofName(v_mod_2618_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_Name_isAnonymous(v_hint_2620_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2703_ = l_Lean_MessageData_ofName(v_hint_2620_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___y_2688_ = v___x_2700_;
v___y_2689_ = v___x_2704_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2705_; 
lean_dec(v_hint_2620_);
v___x_2705_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2688_ = v___x_2700_;
v___y_2689_ = v___x_2705_;
goto v___jp_2687_;
}
}
}
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref_known(v_entry_2635_, 1);
lean_dec(v_hint_2620_);
lean_dec(v_mod_2618_);
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
v___jp_2639_:
{
lean_object* v___x_2642_; lean_object* v_toEnvExtension_2643_; lean_object* v_env_2644_; lean_object* v_nextMacroScope_2645_; lean_object* v_ngen_2646_; lean_object* v_auxDeclNGen_2647_; lean_object* v_traceState_2648_; lean_object* v_messages_2649_; lean_object* v_infoState_2650_; lean_object* v_snapshotTasks_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2679_; 
v___x_2642_ = lean_st_ref_take(v___y_2641_);
v_toEnvExtension_2643_ = lean_ctor_get(v___x_2636_, 0);
v_env_2644_ = lean_ctor_get(v___x_2642_, 0);
v_nextMacroScope_2645_ = lean_ctor_get(v___x_2642_, 1);
v_ngen_2646_ = lean_ctor_get(v___x_2642_, 2);
v_auxDeclNGen_2647_ = lean_ctor_get(v___x_2642_, 3);
v_traceState_2648_ = lean_ctor_get(v___x_2642_, 4);
v_messages_2649_ = lean_ctor_get(v___x_2642_, 6);
v_infoState_2650_ = lean_ctor_get(v___x_2642_, 7);
v_snapshotTasks_2651_ = lean_ctor_get(v___x_2642_, 8);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v___x_2642_, 5);
lean_dec(v_unused_2680_);
v___x_2653_ = v___x_2642_;
v_isShared_2654_ = v_isSharedCheck_2679_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_snapshotTasks_2651_);
lean_inc(v_infoState_2650_);
lean_inc(v_messages_2649_);
lean_inc(v_traceState_2648_);
lean_inc(v_auxDeclNGen_2647_);
lean_inc(v_ngen_2646_);
lean_inc(v_nextMacroScope_2645_);
lean_inc(v_env_2644_);
lean_dec(v___x_2642_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2679_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_asyncMode_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v_asyncMode_2655_ = lean_ctor_get(v_toEnvExtension_2643_, 2);
v___x_2656_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2636_, v_env_2644_, v_entry_2635_, v_asyncMode_2655_, v___x_2638_);
v___x_2657_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 5, v___x_2657_);
lean_ctor_set(v___x_2653_, 0, v___x_2656_);
v___x_2659_ = v___x_2653_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_nextMacroScope_2645_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v_ngen_2646_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_auxDeclNGen_2647_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v_traceState_2648_);
lean_ctor_set(v_reuseFailAlloc_2678_, 5, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2678_, 6, v_messages_2649_);
lean_ctor_set(v_reuseFailAlloc_2678_, 7, v_infoState_2650_);
lean_ctor_set(v_reuseFailAlloc_2678_, 8, v_snapshotTasks_2651_);
v___x_2659_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v_mctx_2662_; lean_object* v_zetaDeltaFVarIds_2663_; lean_object* v_postponed_2664_; lean_object* v_diag_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2676_; 
v___x_2660_ = lean_st_ref_put(v___y_2641_, v___x_2659_);
v___x_2661_ = lean_st_ref_take(v___y_2640_);
v_mctx_2662_ = lean_ctor_get(v___x_2661_, 0);
v_zetaDeltaFVarIds_2663_ = lean_ctor_get(v___x_2661_, 2);
v_postponed_2664_ = lean_ctor_get(v___x_2661_, 3);
v_diag_2665_ = lean_ctor_get(v___x_2661_, 4);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2661_, 1);
lean_dec(v_unused_2677_);
v___x_2667_ = v___x_2661_;
v_isShared_2668_ = v_isSharedCheck_2676_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_diag_2665_);
lean_inc(v_postponed_2664_);
lean_inc(v_zetaDeltaFVarIds_2663_);
lean_inc(v_mctx_2662_);
lean_dec(v___x_2661_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2676_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2669_);
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_mctx_2662_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_zetaDeltaFVarIds_2663_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_postponed_2664_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_diag_2665_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_st_ref_put(v___y_2640_, v___x_2671_);
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2721_, lean_object* v_isMeta_2722_, lean_object* v_hint_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v_isMeta_boxed_2732_; lean_object* v_res_2733_; 
v_isMeta_boxed_2732_ = lean_unbox(v_isMeta_2722_);
v_res_2733_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2721_, v_isMeta_boxed_2732_, v_hint_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2734_, lean_object* v_declName_2735_, lean_object* v_as_2736_, size_t v_sz_2737_, size_t v_i_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v___x_2748_; 
v___x_2748_ = lean_usize_dec_lt(v_i_2738_, v_sz_2737_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v_declName_2735_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_b_2739_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; lean_object* v_modules_2751_; lean_object* v___x_2752_; lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v_toImport_2755_; lean_object* v_module_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2750_ = l_Lean_Environment_header(v___x_2734_);
v_modules_2751_ = lean_ctor_get(v___x_2750_, 3);
lean_inc_ref(v_modules_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2753_ = lean_array_uget_borrowed(v_as_2736_, v_i_2738_);
v___x_2754_ = lean_array_get(v___x_2752_, v_modules_2751_, v_a_2753_);
lean_dec_ref(v_modules_2751_);
v_toImport_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_ref(v_toImport_2755_);
lean_dec(v___x_2754_);
v_module_2756_ = lean_ctor_get(v_toImport_2755_, 0);
lean_inc(v_module_2756_);
lean_dec_ref(v_toImport_2755_);
v___x_2757_ = 0;
lean_inc(v_declName_2735_);
v___x_2758_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2756_, v___x_2757_, v_declName_2735_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; 
lean_dec_ref_known(v___x_2758_, 1);
v___x_2759_ = lean_box(0);
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_add(v_i_2738_, v___x_2760_);
v_i_2738_ = v___x_2761_;
v_b_2739_ = v___x_2759_;
goto _start;
}
else
{
lean_dec(v_declName_2735_);
return v___x_2758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2763_, lean_object* v_declName_2764_, lean_object* v_as_2765_, lean_object* v_sz_2766_, lean_object* v_i_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
size_t v_sz_boxed_2777_; size_t v_i_boxed_2778_; lean_object* v_res_2779_; 
v_sz_boxed_2777_ = lean_unbox_usize(v_sz_2766_);
lean_dec(v_sz_2766_);
v_i_boxed_2778_ = lean_unbox_usize(v_i_2767_);
lean_dec(v_i_2767_);
v_res_2779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2763_, v_declName_2764_, v_as_2765_, v_sz_boxed_2777_, v_i_boxed_2778_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_as_2765_);
lean_dec_ref(v___x_2763_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg(lean_object* v_m_2780_, lean_object* v_query_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v_zero_2785_; uint8_t v_isZero_2786_; 
v_zero_2785_ = lean_unsigned_to_nat(0u);
v_isZero_2786_ = lean_nat_dec_eq(v_x_2783_, v_zero_2785_);
if (v_isZero_2786_ == 1)
{
lean_dec(v_x_2784_);
lean_dec(v_x_2783_);
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_box(2);
return v___x_2787_;
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_val_2788_ = lean_ctor_get(v_x_2782_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v_x_2782_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_val_2788_);
lean_dec(v_x_2782_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_val_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_keyArray_2796_; lean_object* v_valueArray_2797_; lean_object* v___x_2798_; uint8_t v_isSome_2799_; 
v_keyArray_2796_ = lean_ctor_get(v_m_2780_, 1);
v_valueArray_2797_ = lean_ctor_get(v_m_2780_, 2);
v___x_2798_ = lean_array_fget_borrowed(v_keyArray_2796_, v_x_2784_);
v_isSome_2799_ = lean_noption_is_some(v___x_2798_);
if (v_isSome_2799_ == 0)
{
lean_dec(v_x_2783_);
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_x_2784_);
return v___x_2800_;
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_x_2784_);
v_val_2801_ = lean_ctor_get(v_x_2782_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_x_2782_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v_x_2782_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_val_2801_);
lean_dec(v_x_2782_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_val_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_one_2809_; lean_object* v_n_2810_; lean_object* v___y_2812_; 
v_one_2809_ = lean_unsigned_to_nat(1u);
v_n_2810_ = lean_nat_sub(v_x_2783_, v_one_2809_);
lean_dec(v_x_2783_);
if (v_isSome_2799_ == 0)
{
goto v___jp_2818_;
}
else
{
lean_object* v___x_2820_; uint8_t v_isSome_2821_; 
v___x_2820_ = lean_array_fget_borrowed(v_valueArray_2797_, v_x_2784_);
v_isSome_2821_ = lean_noption_is_some(v___x_2820_);
if (v_isSome_2821_ == 0)
{
goto v___jp_2818_;
}
else
{
lean_object* v_val_2822_; uint8_t v___x_2823_; 
lean_inc(v___x_2798_);
v_val_2822_ = lean_noption_get(v___x_2798_);
v___x_2823_ = lean_name_eq(v_val_2822_, v_query_2781_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
lean_dec(v_val_2822_);
v___x_2824_ = lean_array_get_size(v_keyArray_2796_);
v___x_2825_ = lean_nat_add(v_x_2784_, v_one_2809_);
lean_dec(v_x_2784_);
v___x_2826_ = lean_nat_dec_lt(v___x_2825_, v___x_2824_);
if (v___x_2826_ == 0)
{
lean_dec(v___x_2825_);
v_x_2783_ = v_n_2810_;
v_x_2784_ = v_zero_2785_;
goto _start;
}
else
{
v_x_2783_ = v_n_2810_;
v_x_2784_ = v___x_2825_;
goto _start;
}
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2830_; 
lean_dec(v_n_2810_);
lean_dec(v_x_2782_);
lean_inc(v___x_2820_);
v_val_2829_ = lean_noption_get(v___x_2820_);
v___x_2830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2830_, 0, v_x_2784_);
lean_ctor_set(v___x_2830_, 1, v_val_2822_);
lean_ctor_set(v___x_2830_, 2, v_val_2829_);
return v___x_2830_;
}
}
}
v___jp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2813_ = lean_array_get_size(v_keyArray_2796_);
v___x_2814_ = lean_nat_add(v_x_2784_, v_one_2809_);
lean_dec(v_x_2784_);
v___x_2815_ = lean_nat_dec_lt(v___x_2814_, v___x_2813_);
if (v___x_2815_ == 0)
{
lean_dec(v___x_2814_);
v_x_2782_ = v___y_2812_;
v_x_2783_ = v_n_2810_;
v_x_2784_ = v_zero_2785_;
goto _start;
}
else
{
v_x_2782_ = v___y_2812_;
v_x_2783_ = v_n_2810_;
v_x_2784_ = v___x_2814_;
goto _start;
}
}
v___jp_2818_:
{
if (lean_obj_tag(v_x_2782_) == 0)
{
lean_object* v___x_2819_; 
lean_inc(v_x_2784_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_x_2784_);
v___y_2812_ = v___x_2819_;
goto v___jp_2811_;
}
else
{
v___y_2812_ = v_x_2782_;
goto v___jp_2811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg___boxed(lean_object* v_m_2831_, lean_object* v_query_2832_, lean_object* v_x_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg(v_m_2831_, v_query_2832_, v_x_2833_, v_x_2834_, v_x_2835_);
lean_dec(v_query_2832_);
lean_dec_ref(v_m_2831_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg(lean_object* v_m_2837_, lean_object* v_query_2838_){
_start:
{
lean_object* v_keyArray_2839_; lean_object* v___x_2840_; uint64_t v___y_2842_; 
v_keyArray_2839_ = lean_ctor_get(v_m_2837_, 1);
v___x_2840_ = lean_array_get_size(v_keyArray_2839_);
if (lean_obj_tag(v_query_2838_) == 0)
{
uint64_t v___x_2857_; 
v___x_2857_ = 1723ULL;
v___y_2842_ = v___x_2857_;
goto v___jp_2841_;
}
else
{
uint64_t v_hash_2858_; 
v_hash_2858_ = lean_ctor_get_uint64(v_query_2838_, sizeof(void*)*2);
v___y_2842_ = v_hash_2858_;
goto v___jp_2841_;
}
v___jp_2841_:
{
uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v_fold_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2843_ = 32ULL;
v___x_2844_ = lean_uint64_shift_right(v___y_2842_, v___x_2843_);
v_fold_2845_ = lean_uint64_xor(v___y_2842_, v___x_2844_);
v___x_2846_ = 16ULL;
v___x_2847_ = lean_uint64_shift_right(v_fold_2845_, v___x_2846_);
v___x_2848_ = lean_uint64_xor(v_fold_2845_, v___x_2847_);
v___x_2849_ = lean_uint64_to_usize(v___x_2848_);
v___x_2850_ = lean_usize_of_nat(v___x_2840_);
v___x_2851_ = ((size_t)1ULL);
v___x_2852_ = lean_usize_sub(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_usize_land(v___x_2849_, v___x_2852_);
v___x_2854_ = lean_usize_to_nat(v___x_2853_);
v___x_2855_ = lean_box(0);
v___x_2856_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg(v_m_2837_, v_query_2838_, v___x_2855_, v___x_2840_, v___x_2854_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg___boxed(lean_object* v_m_2859_, lean_object* v_query_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg(v_m_2859_, v_query_2860_);
lean_dec(v_query_2860_);
lean_dec_ref(v_m_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_m_2862_, lean_object* v_query_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg(v_m_2862_, v_query_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_index_2865_; lean_object* v_key_2866_; lean_object* v_value_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_index_2865_ = lean_ctor_get(v___x_2864_, 0);
v_key_2866_ = lean_ctor_get(v___x_2864_, 1);
v_value_2867_ = lean_ctor_get(v___x_2864_, 2);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2864_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_value_2867_);
lean_inc(v_key_2866_);
lean_inc(v_index_2865_);
lean_dec(v___x_2864_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_index_2865_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_key_2866_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_value_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v___x_2875_; 
lean_dec(v___x_2864_);
v___x_2875_ = lean_box(1);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_m_2876_, lean_object* v_query_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_m_2876_, v_query_2877_);
lean_dec(v_query_2877_);
lean_dec_ref(v_m_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_m_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_value_2882_; lean_object* v___x_2883_; 
v_value_2882_ = lean_ctor_get(v___x_2881_, 2);
lean_inc(v_value_2882_);
lean_dec_ref_known(v___x_2881_, 3);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_value_2882_);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_box(0);
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_m_2885_);
return v_res_2887_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2891_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2892_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2891_, v___x_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2895_, uint8_t v_isMeta_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v_env_2909_; lean_object* v___y_2911_; lean_object* v___x_2924_; 
v___x_2905_ = lean_st_ref_get(v___y_2903_);
v_env_2909_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2905_);
v___x_2924_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2909_, v_declName_2895_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_dec_ref(v_env_2909_);
lean_dec(v_declName_2895_);
goto v___jp_2906_;
}
else
{
lean_object* v_val_2925_; lean_object* v___x_2926_; lean_object* v_modules_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_val_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_val_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Environment_header(v_env_2909_);
v_modules_2927_ = lean_ctor_get(v___x_2926_, 3);
lean_inc_ref(v_modules_2927_);
lean_dec_ref(v___x_2926_);
v___x_2928_ = lean_array_get_size(v_modules_2927_);
v___x_2929_ = lean_nat_dec_lt(v_val_2925_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v_modules_2927_);
lean_dec(v_val_2925_);
lean_dec_ref(v_env_2909_);
lean_dec(v_declName_2895_);
goto v___jp_2906_;
}
else
{
lean_object* v___x_2930_; lean_object* v_env_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___y_2935_; 
v___x_2930_ = lean_st_ref_get(v___y_2903_);
v_env_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2930_);
v___x_2932_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2933_ = lean_array_fget(v_modules_2927_, v_val_2925_);
lean_dec(v_val_2925_);
lean_dec_ref(v_modules_2927_);
if (v_isMeta_2896_ == 0)
{
lean_dec_ref(v_env_2931_);
v___y_2935_ = v_isMeta_2896_;
goto v___jp_2934_;
}
else
{
uint8_t v___x_2946_; 
lean_inc(v_declName_2895_);
v___x_2946_ = l_Lean_isMarkedMeta(v_env_2931_, v_declName_2895_);
if (v___x_2946_ == 0)
{
v___y_2935_ = v_isMeta_2896_;
goto v___jp_2934_;
}
else
{
uint8_t v___x_2947_; 
v___x_2947_ = 0;
v___y_2935_ = v___x_2947_;
goto v___jp_2934_;
}
}
v___jp_2934_:
{
lean_object* v_toImport_2936_; lean_object* v_module_2937_; lean_object* v___x_2938_; 
v_toImport_2936_ = lean_ctor_get(v___x_2933_, 0);
lean_inc_ref(v_toImport_2936_);
lean_dec(v___x_2933_);
v_module_2937_ = lean_ctor_get(v_toImport_2936_, 0);
lean_inc(v_module_2937_);
lean_dec_ref(v_toImport_2936_);
lean_inc(v_declName_2895_);
v___x_2938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2937_, v___y_2935_, v_declName_2895_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec_ref_known(v___x_2938_, 1);
v___x_2939_ = l_Lean_indirectModUseExt;
v___x_2940_ = lean_box(1);
v___x_2941_ = lean_box(0);
lean_inc_ref(v_env_2909_);
v___x_2942_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2932_, v___x_2939_, v_env_2909_, v___x_2940_, v___x_2941_);
v___x_2943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_2942_, v_declName_2895_);
lean_dec(v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; 
v___x_2944_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2911_ = v___x_2944_;
goto v___jp_2910_;
}
else
{
lean_object* v_val_2945_; 
v_val_2945_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_val_2945_);
lean_dec_ref_known(v___x_2943_, 1);
v___y_2911_ = v_val_2945_;
goto v___jp_2910_;
}
}
else
{
lean_dec_ref(v_env_2909_);
lean_dec(v_declName_2895_);
return v___x_2938_;
}
}
}
}
v___jp_2906_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
v___jp_2910_:
{
lean_object* v___x_2912_; size_t v_sz_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v___x_2912_ = lean_box(0);
v_sz_2913_ = lean_array_size(v___y_2911_);
v___x_2914_ = ((size_t)0ULL);
v___x_2915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2909_, v_declName_2895_, v___y_2911_, v_sz_2913_, v___x_2914_, v___x_2912_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec_ref(v___y_2911_);
lean_dec_ref(v_env_2909_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2923_);
v___x_2917_ = v___x_2915_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v___x_2915_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2912_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2912_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2948_, lean_object* v_isMeta_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
uint8_t v_isMeta_boxed_2958_; lean_object* v_res_2959_; 
v_isMeta_boxed_2958_ = lean_unbox(v_isMeta_2949_);
v_res_2959_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2948_, v_isMeta_boxed_2958_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2960_, lean_object* v_b_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
if (lean_obj_tag(v_as_x27_2960_) == 0)
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_b_2961_);
return v___x_2970_;
}
else
{
lean_object* v_head_2971_; lean_object* v_tail_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; 
v_head_2971_ = lean_ctor_get(v_as_x27_2960_, 0);
v_tail_2972_ = lean_ctor_get(v_as_x27_2960_, 1);
v___x_2973_ = 1;
lean_inc(v_head_2971_);
v___x_2974_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2971_, v___x_2973_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = lean_box(0);
v_as_x27_2960_ = v_tail_2972_;
v_b_2961_ = v___x_2975_;
goto _start;
}
else
{
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2977_, v_b_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v_as_x27_2977_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
if (lean_obj_tag(v_as_2988_) == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
else
{
lean_object* v_options_2999_; uint8_t v_hasTrace_3000_; 
v_options_2999_ = lean_ctor_get(v___y_2994_, 2);
v_hasTrace_3000_ = lean_ctor_get_uint8(v_options_2999_, sizeof(void*)*1);
if (v_hasTrace_3000_ == 0)
{
lean_object* v_tail_3001_; 
v_tail_3001_ = lean_ctor_get(v_as_2988_, 1);
lean_inc(v_tail_3001_);
lean_dec_ref_known(v_as_2988_, 2);
v_as_2988_ = v_tail_3001_;
goto _start;
}
else
{
lean_object* v_head_3003_; lean_object* v_tail_3004_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v_inheritedTraceOptions_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_head_3003_ = lean_ctor_get(v_as_2988_, 0);
lean_inc(v_head_3003_);
v_tail_3004_ = lean_ctor_get(v_as_2988_, 1);
lean_inc(v_tail_3004_);
lean_dec_ref_known(v_as_2988_, 2);
v_fst_3005_ = lean_ctor_get(v_head_3003_, 0);
lean_inc_n(v_fst_3005_, 2);
v_snd_3006_ = lean_ctor_get(v_head_3003_, 1);
lean_inc(v_snd_3006_);
lean_dec(v_head_3003_);
v_inheritedTraceOptions_3007_ = lean_ctor_get(v___y_2994_, 13);
v___x_3008_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_3009_ = l_Lean_Name_append(v___x_3008_, v_fst_3005_);
v___x_3010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3007_, v_options_2999_, v___x_3009_);
lean_dec(v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec(v_snd_3006_);
lean_dec(v_fst_3005_);
v_as_2988_ = v_tail_3004_;
goto _start;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_snd_3006_);
v___x_3013_ = l_Lean_MessageData_ofFormat(v___x_3012_);
v___x_3014_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_3005_, v___x_3013_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_dec_ref_known(v___x_3014_, 1);
v_as_2988_ = v_tail_3004_;
goto _start;
}
else
{
lean_dec(v_tail_3004_);
return v___x_3014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec_ref(v___y_3017_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_3026_, lean_object* v_msg_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_fileName_3033_; lean_object* v_fileMap_3034_; lean_object* v_options_3035_; lean_object* v_currRecDepth_3036_; lean_object* v_maxRecDepth_3037_; lean_object* v_ref_3038_; lean_object* v_currNamespace_3039_; lean_object* v_openDecls_3040_; lean_object* v_initHeartbeats_3041_; lean_object* v_maxHeartbeats_3042_; lean_object* v_quotContext_3043_; lean_object* v_currMacroScope_3044_; uint8_t v_diag_3045_; lean_object* v_cancelTk_x3f_3046_; uint8_t v_suppressElabErrors_3047_; lean_object* v_inheritedTraceOptions_3048_; lean_object* v_ref_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_fileName_3033_ = lean_ctor_get(v___y_3030_, 0);
v_fileMap_3034_ = lean_ctor_get(v___y_3030_, 1);
v_options_3035_ = lean_ctor_get(v___y_3030_, 2);
v_currRecDepth_3036_ = lean_ctor_get(v___y_3030_, 3);
v_maxRecDepth_3037_ = lean_ctor_get(v___y_3030_, 4);
v_ref_3038_ = lean_ctor_get(v___y_3030_, 5);
v_currNamespace_3039_ = lean_ctor_get(v___y_3030_, 6);
v_openDecls_3040_ = lean_ctor_get(v___y_3030_, 7);
v_initHeartbeats_3041_ = lean_ctor_get(v___y_3030_, 8);
v_maxHeartbeats_3042_ = lean_ctor_get(v___y_3030_, 9);
v_quotContext_3043_ = lean_ctor_get(v___y_3030_, 10);
v_currMacroScope_3044_ = lean_ctor_get(v___y_3030_, 11);
v_diag_3045_ = lean_ctor_get_uint8(v___y_3030_, sizeof(void*)*14);
v_cancelTk_x3f_3046_ = lean_ctor_get(v___y_3030_, 12);
v_suppressElabErrors_3047_ = lean_ctor_get_uint8(v___y_3030_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3048_ = lean_ctor_get(v___y_3030_, 13);
v_ref_3049_ = l_Lean_replaceRef(v_ref_3026_, v_ref_3038_);
lean_inc_ref(v_inheritedTraceOptions_3048_);
lean_inc(v_cancelTk_x3f_3046_);
lean_inc(v_currMacroScope_3044_);
lean_inc(v_quotContext_3043_);
lean_inc(v_maxHeartbeats_3042_);
lean_inc(v_initHeartbeats_3041_);
lean_inc(v_openDecls_3040_);
lean_inc(v_currNamespace_3039_);
lean_inc(v_maxRecDepth_3037_);
lean_inc(v_currRecDepth_3036_);
lean_inc_ref(v_options_3035_);
lean_inc_ref(v_fileMap_3034_);
lean_inc_ref(v_fileName_3033_);
v___x_3050_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3050_, 0, v_fileName_3033_);
lean_ctor_set(v___x_3050_, 1, v_fileMap_3034_);
lean_ctor_set(v___x_3050_, 2, v_options_3035_);
lean_ctor_set(v___x_3050_, 3, v_currRecDepth_3036_);
lean_ctor_set(v___x_3050_, 4, v_maxRecDepth_3037_);
lean_ctor_set(v___x_3050_, 5, v_ref_3049_);
lean_ctor_set(v___x_3050_, 6, v_currNamespace_3039_);
lean_ctor_set(v___x_3050_, 7, v_openDecls_3040_);
lean_ctor_set(v___x_3050_, 8, v_initHeartbeats_3041_);
lean_ctor_set(v___x_3050_, 9, v_maxHeartbeats_3042_);
lean_ctor_set(v___x_3050_, 10, v_quotContext_3043_);
lean_ctor_set(v___x_3050_, 11, v_currMacroScope_3044_);
lean_ctor_set(v___x_3050_, 12, v_cancelTk_x3f_3046_);
lean_ctor_set(v___x_3050_, 13, v_inheritedTraceOptions_3048_);
lean_ctor_set_uint8(v___x_3050_, sizeof(void*)*14, v_diag_3045_);
lean_ctor_set_uint8(v___x_3050_, sizeof(void*)*14 + 1, v_suppressElabErrors_3047_);
v___x_3051_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_3027_, v___y_3028_, v___y_3029_, v___x_3050_, v___y_3031_);
lean_dec_ref_known(v___x_3050_, 14);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_3052_, lean_object* v_msg_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3052_, v_msg_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v_ref_3052_);
return v_res_3059_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = l_Lean_maxRecDepthErrorMessage;
v___x_3066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_3068_ = l_Lean_MessageData_ofFormat(v___x_3067_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3070_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3071_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_ref_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v_env_3091_; lean_object* v_options_3092_; lean_object* v_currRecDepth_3093_; lean_object* v_maxRecDepth_3094_; lean_object* v_ref_3095_; lean_object* v_currNamespace_3096_; lean_object* v_openDecls_3097_; lean_object* v_quotContext_3098_; lean_object* v_currMacroScope_3099_; lean_object* v___x_3100_; lean_object* v_nextMacroScope_3101_; lean_object* v___f_3102_; lean_object* v___f_3103_; lean_object* v___f_3104_; lean_object* v___f_3105_; lean_object* v___f_3106_; lean_object* v_methods_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3090_ = lean_st_ref_get(v___y_3088_);
v_env_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc_ref_n(v_env_3091_, 4);
lean_dec(v___x_3090_);
v_options_3092_ = lean_ctor_get(v___y_3087_, 2);
v_currRecDepth_3093_ = lean_ctor_get(v___y_3087_, 3);
v_maxRecDepth_3094_ = lean_ctor_get(v___y_3087_, 4);
v_ref_3095_ = lean_ctor_get(v___y_3087_, 5);
v_currNamespace_3096_ = lean_ctor_get(v___y_3087_, 6);
v_openDecls_3097_ = lean_ctor_get(v___y_3087_, 7);
v_quotContext_3098_ = lean_ctor_get(v___y_3087_, 10);
v_currMacroScope_3099_ = lean_ctor_get(v___y_3087_, 11);
v___x_3100_ = lean_st_ref_get(v___y_3088_);
v_nextMacroScope_3101_ = lean_ctor_get(v___x_3100_, 1);
lean_inc(v_nextMacroScope_3101_);
lean_dec(v___x_3100_);
v___f_3102_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3102_, 0, v_env_3091_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3103_, 0, v_env_3091_);
lean_inc_n(v_openDecls_3097_, 2);
lean_inc_n(v_currNamespace_3096_, 3);
v___f_3104_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3104_, 0, v_env_3091_);
lean_closure_set(v___f_3104_, 1, v_currNamespace_3096_);
lean_closure_set(v___f_3104_, 2, v_openDecls_3097_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3105_, 0, v_currNamespace_3096_);
lean_inc_ref(v_options_3092_);
v___f_3106_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3106_, 0, v_env_3091_);
lean_closure_set(v___f_3106_, 1, v_options_3092_);
lean_closure_set(v___f_3106_, 2, v_currNamespace_3096_);
lean_closure_set(v___f_3106_, 3, v_openDecls_3097_);
v_methods_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3107_, 0, v___f_3102_);
lean_ctor_set(v_methods_3107_, 1, v___f_3105_);
lean_ctor_set(v_methods_3107_, 2, v___f_3103_);
lean_ctor_set(v_methods_3107_, 3, v___f_3104_);
lean_ctor_set(v_methods_3107_, 4, v___f_3106_);
lean_inc(v_ref_3095_);
lean_inc(v_maxRecDepth_3094_);
lean_inc(v_currRecDepth_3093_);
lean_inc(v_currMacroScope_3099_);
lean_inc(v_quotContext_3098_);
v___x_3108_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3108_, 0, v_methods_3107_);
lean_ctor_set(v___x_3108_, 1, v_quotContext_3098_);
lean_ctor_set(v___x_3108_, 2, v_currMacroScope_3099_);
lean_ctor_set(v___x_3108_, 3, v_currRecDepth_3093_);
lean_ctor_set(v___x_3108_, 4, v_maxRecDepth_3094_);
lean_ctor_set(v___x_3108_, 5, v_ref_3095_);
v___x_3109_ = lean_box(0);
v___x_3110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3110_, 0, v_nextMacroScope_3101_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
lean_ctor_set(v___x_3110_, 2, v___x_3109_);
v___x_3111_ = lean_apply_2(v_x_3081_, v___x_3108_, v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v_a_3113_; lean_object* v_macroScope_3114_; lean_object* v_traceMsgs_3115_; lean_object* v_expandedMacroDecls_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 1);
lean_inc(v_a_3112_);
v_a_3113_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3111_, 2);
v_macroScope_3114_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_macroScope_3114_);
v_traceMsgs_3115_ = lean_ctor_get(v_a_3112_, 1);
lean_inc(v_traceMsgs_3115_);
v_expandedMacroDecls_3116_ = lean_ctor_get(v_a_3112_, 2);
lean_inc(v_expandedMacroDecls_3116_);
lean_dec(v_a_3112_);
v___x_3117_ = lean_box(0);
v___x_3118_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3116_, v___x_3117_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v_expandedMacroDecls_3116_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v___x_3119_; lean_object* v_env_3120_; lean_object* v_ngen_3121_; lean_object* v_auxDeclNGen_3122_; lean_object* v_traceState_3123_; lean_object* v_cache_3124_; lean_object* v_messages_3125_; lean_object* v_infoState_3126_; lean_object* v_snapshotTasks_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref_known(v___x_3118_, 1);
v___x_3119_ = lean_st_ref_take(v___y_3088_);
v_env_3120_ = lean_ctor_get(v___x_3119_, 0);
v_ngen_3121_ = lean_ctor_get(v___x_3119_, 2);
v_auxDeclNGen_3122_ = lean_ctor_get(v___x_3119_, 3);
v_traceState_3123_ = lean_ctor_get(v___x_3119_, 4);
v_cache_3124_ = lean_ctor_get(v___x_3119_, 5);
v_messages_3125_ = lean_ctor_get(v___x_3119_, 6);
v_infoState_3126_ = lean_ctor_get(v___x_3119_, 7);
v_snapshotTasks_3127_ = lean_ctor_get(v___x_3119_, 8);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v___x_3119_, 1);
lean_dec(v_unused_3154_);
v___x_3129_ = v___x_3119_;
v_isShared_3130_ = v_isSharedCheck_3153_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_snapshotTasks_3127_);
lean_inc(v_infoState_3126_);
lean_inc(v_messages_3125_);
lean_inc(v_cache_3124_);
lean_inc(v_traceState_3123_);
lean_inc(v_auxDeclNGen_3122_);
lean_inc(v_ngen_3121_);
lean_inc(v_env_3120_);
lean_dec(v___x_3119_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3153_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 1, v_macroScope_3114_);
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_env_3120_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_macroScope_3114_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v_ngen_3121_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v_auxDeclNGen_3122_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v_traceState_3123_);
lean_ctor_set(v_reuseFailAlloc_3152_, 5, v_cache_3124_);
lean_ctor_set(v_reuseFailAlloc_3152_, 6, v_messages_3125_);
lean_ctor_set(v_reuseFailAlloc_3152_, 7, v_infoState_3126_);
lean_ctor_set(v_reuseFailAlloc_3152_, 8, v_snapshotTasks_3127_);
v___x_3132_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_st_ref_put(v___y_3088_, v___x_3132_);
v___x_3134_ = l_List_reverse___redArg(v_traceMsgs_3115_);
v___x_3135_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3134_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; 
v_unused_3143_ = lean_ctor_get(v___x_3135_, 0);
lean_dec(v_unused_3143_);
v___x_3137_ = v___x_3135_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_dec(v___x_3135_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_a_3113_);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3113_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3113_);
v_a_3144_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_traceMsgs_3115_);
lean_dec(v_macroScope_3114_);
lean_dec(v_a_3113_);
v_a_3155_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3118_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3118_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; 
v_a_3163_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3111_, 2);
if (lean_obj_tag(v_a_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_a_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_a_3164_ = lean_ctor_get(v_a_3163_, 0);
lean_inc(v_a_3164_);
v_a_3165_ = lean_ctor_get(v_a_3163_, 1);
lean_inc_ref(v_a_3165_);
lean_dec_ref_known(v_a_3163_, 2);
v___x_3166_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3167_ = lean_string_dec_eq(v_a_3165_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_a_3165_);
v___x_3169_ = l_Lean_MessageData_ofFormat(v___x_3168_);
v___x_3170_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3164_, v___x_3169_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v_a_3164_);
return v___x_3170_;
}
else
{
lean_object* v___x_3171_; 
lean_dec_ref(v_a_3165_);
v___x_3171_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3164_);
return v___x_3171_;
}
}
else
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_quotContext_3187_; lean_object* v_currMacroScope_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_quotContext_3187_ = lean_ctor_get(v___y_3184_, 10);
lean_inc(v_quotContext_3187_);
v_currMacroScope_3188_ = lean_ctor_get(v___y_3184_, 11);
lean_inc(v_currMacroScope_3188_);
lean_dec_ref(v___y_3184_);
v___x_3189_ = l_Lean_addMacroScope(v_quotContext_3187_, v___x_3183_, v_currMacroScope_3188_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___f_3204_; lean_object* v___x_3205_; 
v___f_3204_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3205_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3204_, v___y_3201_, v___y_3202_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3210_, uint8_t v_canonical_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3229_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3229_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3229_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3225_ = l_Lean_mkIdentFrom(v_ref_3210_, v_a_3221_, v_canonical_3211_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3225_);
v___x_3227_ = v___x_3223_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
v_a_3230_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3220_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3220_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3238_, lean_object* v_canonical_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v_canonical_boxed_3248_; lean_object* v_res_3249_; 
v_canonical_boxed_3248_ = lean_unbox(v_canonical_3239_);
v_res_3249_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3238_, v_canonical_boxed_3248_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v_ref_3238_);
return v_res_3249_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3262_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_3263_ = l_Lean_Name_append(v___x_3262_, v___x_3261_);
return v___x_3263_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3269_ = l_Lean_stringToMessageData(v___x_3268_);
return v___x_3269_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3272_ = l_Lean_stringToMessageData(v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3273_, lean_object* v_letOrReassign_3274_, lean_object* v_decl_3275_, lean_object* v_tk_3276_, lean_object* v_dec_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3273_, v_letOrReassign_3274_, v_decl_3275_, v_tk_3276_, v_dec_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec_ref(v_a_3278_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3287_, lean_object* v_letOrReassign_3288_, lean_object* v_decl_3289_, lean_object* v_tk_3290_, lean_object* v_dec_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3287_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; 
lean_dec_ref_known(v___x_3300_, 1);
lean_inc(v_decl_3289_);
v___x_3301_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3289_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3288_, v_a_3302_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3303_, 1);
v___x_3304_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3291_, v_tk_3290_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3288_, v_decl_3289_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v_doBlockResultType_3308_; lean_object* v___x_3309_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v_doBlockResultType_3308_ = lean_ctor_get(v_a_3292_, 3);
lean_inc_ref(v_doBlockResultType_3308_);
v___x_3309_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3308_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3528_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3528_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3528_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3307_);
v___x_3318_ = l_Lean_Syntax_isOfKind(v_a_3307_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3307_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_tk_3290_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v___x_3319_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = l_Lean_Syntax_getArg(v_a_3307_, v___x_3320_);
lean_dec(v_a_3307_);
v___x_3322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3321_);
v___x_3323_ = l_Lean_Syntax_isOfKind(v___x_3321_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
lean_dec(v_tk_3290_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3321_);
v___x_3325_ = l_Lean_Syntax_isOfKind(v___x_3321_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3321_);
v___x_3327_ = l_Lean_Syntax_isOfKind(v___x_3321_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_dec(v___x_3321_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v___x_3328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v_id_3330_; lean_object* v_binders_3331_; lean_object* v_type_3332_; lean_object* v_value_3333_; lean_object* v___y_3335_; uint8_t v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v_id_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; uint8_t v___x_3424_; 
v___x_3329_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3321_);
lean_dec(v___x_3321_);
v_id_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_id_3330_);
v_binders_3331_ = lean_ctor_get(v___x_3329_, 1);
lean_inc_ref(v_binders_3331_);
v_type_3332_ = lean_ctor_get(v___x_3329_, 2);
lean_inc(v_type_3332_);
v_value_3333_ = lean_ctor_get(v___x_3329_, 3);
lean_inc(v_value_3333_);
lean_dec_ref(v___x_3329_);
v___x_3424_ = l_Lean_Syntax_isIdent(v_id_3330_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3330_, v___x_3318_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
lean_dec(v_id_3330_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_id_3406_ = v_a_3426_;
v___y_3407_ = v_a_3292_;
v___y_3408_ = v_a_3293_;
v___y_3409_ = v_a_3294_;
v___y_3410_ = v_a_3295_;
v___y_3411_ = v_a_3296_;
v___y_3412_ = v_a_3297_;
v___y_3413_ = v_a_3298_;
goto v___jp_3405_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_value_3333_);
lean_dec(v_type_3332_);
lean_dec_ref(v_binders_3331_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3427_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
v_id_3406_ = v_id_3330_;
v___y_3407_ = v_a_3292_;
v___y_3408_ = v_a_3293_;
v___y_3409_ = v_a_3294_;
v___y_3410_ = v_a_3295_;
v___y_3411_ = v_a_3296_;
v___y_3412_ = v_a_3297_;
v___y_3413_ = v_a_3298_;
goto v___jp_3405_;
}
v___jp_3334_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___f_3351_; lean_object* v___x_3352_; 
v___x_3348_ = lean_box(v___x_3318_);
v___x_3349_ = lean_box(v___x_3323_);
v___x_3350_ = lean_box(v___y_3347_);
v___f_3351_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3351_, 0, v_type_3332_);
lean_closure_set(v___f_3351_, 1, v_value_3333_);
lean_closure_set(v___f_3351_, 2, v___x_3348_);
lean_closure_set(v___f_3351_, 3, v___x_3349_);
lean_closure_set(v___f_3351_, 4, v___x_3320_);
lean_closure_set(v___f_3351_, 5, v___x_3350_);
v___x_3352_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3331_, v___f_3351_, v___y_3340_, v___y_3343_, v___y_3342_, v___y_3344_, v___y_3346_, v___y_3339_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v_options_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3396_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
v_options_3354_ = lean_ctor_get(v___y_3346_, 2);
v_fst_3355_ = lean_ctor_get(v_a_3353_, 0);
v_snd_3356_ = lean_ctor_get(v_a_3353_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3358_ = v_a_3353_;
v_isShared_3359_ = v_isSharedCheck_3396_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_inc(v_fst_3355_);
lean_dec(v_a_3353_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3396_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v_inheritedTraceOptions_3360_; uint8_t v_hasTrace_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_inheritedTraceOptions_3360_ = lean_ctor_get(v___y_3346_, 13);
v_hasTrace_3361_ = lean_ctor_get_uint8(v_options_3354_, sizeof(void*)*1);
v___x_3362_ = lean_box(v___y_3336_);
v___x_3363_ = lean_box(v___y_3337_);
v___x_3364_ = lean_box(v___x_3323_);
v___x_3365_ = lean_box(v___y_3347_);
v___x_3366_ = lean_box(v___x_3318_);
lean_inc(v_snd_3356_);
v___f_3367_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3367_, 0, v___y_3338_);
lean_closure_set(v___f_3367_, 1, v___y_3335_);
lean_closure_set(v___f_3367_, 2, v_a_3305_);
lean_closure_set(v___f_3367_, 3, v___x_3362_);
lean_closure_set(v___f_3367_, 4, v___x_3363_);
lean_closure_set(v___f_3367_, 5, v___x_3364_);
lean_closure_set(v___f_3367_, 6, v_snd_3356_);
lean_closure_set(v___f_3367_, 7, v___x_3365_);
lean_closure_set(v___f_3367_, 8, v___x_3366_);
lean_closure_set(v___f_3367_, 9, v_letOrReassign_3288_);
lean_closure_set(v___f_3367_, 10, v_a_3302_);
v___x_3368_ = l_Lean_Syntax_getId(v___y_3345_);
lean_dec(v___y_3345_);
v___x_3369_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3368_);
if (v_hasTrace_3361_ == 0)
{
lean_object* v___x_3370_; 
lean_del_object(v___x_3358_);
v___x_3370_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3368_, v_fst_3355_, v_snd_3356_, v___f_3367_, v___y_3347_, v___x_3369_, v___y_3341_, v___y_3340_, v___y_3343_, v___y_3342_, v___y_3344_, v___y_3346_, v___y_3339_);
return v___x_3370_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3372_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3373_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3360_, v_options_3354_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
lean_del_object(v___x_3358_);
v___x_3374_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3368_, v_fst_3355_, v_snd_3356_, v___f_3367_, v___y_3347_, v___x_3369_, v___y_3341_, v___y_3340_, v___y_3343_, v___y_3342_, v___y_3344_, v___y_3346_, v___y_3339_);
return v___x_3374_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_inc(v___x_3368_);
v___x_3375_ = l_Lean_MessageData_ofName(v___x_3368_);
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3359_ == 0)
{
lean_ctor_set_tag(v___x_3358_, 7);
lean_ctor_set(v___x_3358_, 1, v___x_3376_);
lean_ctor_set(v___x_3358_, 0, v___x_3375_);
v___x_3378_ = v___x_3358_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_inc(v_fst_3355_);
v___x_3379_ = l_Lean_MessageData_ofExpr(v_fst_3355_);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
lean_inc(v_snd_3356_);
v___x_3383_ = l_Lean_MessageData_ofExpr(v_snd_3356_);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3371_, v___x_3384_, v___y_3342_, v___y_3344_, v___y_3346_, v___y_3339_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3385_, 1);
v___x_3386_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3368_, v_fst_3355_, v_snd_3356_, v___f_3367_, v___y_3347_, v___x_3369_, v___y_3341_, v___y_3340_, v___y_3343_, v___y_3342_, v___y_3344_, v___y_3346_, v___y_3339_);
return v___x_3386_;
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v___x_3368_);
lean_dec_ref(v___f_3367_);
lean_dec(v_snd_3356_);
lean_dec(v_fst_3355_);
v_a_3387_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3385_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
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
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v___y_3345_);
lean_dec(v___y_3338_);
lean_dec(v___y_3335_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
v_a_3397_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3352_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3352_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
v___jp_3405_:
{
uint8_t v_nondep_3414_; 
v_nondep_3414_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1);
if (v_nondep_3414_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3288_) == 1)
{
uint8_t v_usedOnly_3415_; uint8_t v_zeta_3416_; lean_object* v_eq_x3f_3417_; 
v_usedOnly_3415_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 1);
v_zeta_3416_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 2);
v_eq_x3f_3417_ = lean_ctor_get(v_config_3287_, 0);
lean_inc(v_eq_x3f_3417_);
lean_dec_ref(v_config_3287_);
lean_inc(v_id_3406_);
v___y_3335_ = v_eq_x3f_3417_;
v___y_3336_ = v_zeta_3416_;
v___y_3337_ = v_usedOnly_3415_;
v___y_3338_ = v_id_3406_;
v___y_3339_ = v___y_3413_;
v___y_3340_ = v___y_3408_;
v___y_3341_ = v___y_3407_;
v___y_3342_ = v___y_3410_;
v___y_3343_ = v___y_3409_;
v___y_3344_ = v___y_3411_;
v___y_3345_ = v_id_3406_;
v___y_3346_ = v___y_3412_;
v___y_3347_ = v___x_3318_;
goto v___jp_3334_;
}
else
{
uint8_t v_usedOnly_3418_; uint8_t v_zeta_3419_; lean_object* v_eq_x3f_3420_; 
v_usedOnly_3418_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 1);
v_zeta_3419_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 2);
v_eq_x3f_3420_ = lean_ctor_get(v_config_3287_, 0);
lean_inc(v_eq_x3f_3420_);
lean_dec_ref(v_config_3287_);
lean_inc(v_id_3406_);
v___y_3335_ = v_eq_x3f_3420_;
v___y_3336_ = v_zeta_3419_;
v___y_3337_ = v_usedOnly_3418_;
v___y_3338_ = v_id_3406_;
v___y_3339_ = v___y_3413_;
v___y_3340_ = v___y_3408_;
v___y_3341_ = v___y_3407_;
v___y_3342_ = v___y_3410_;
v___y_3343_ = v___y_3409_;
v___y_3344_ = v___y_3411_;
v___y_3345_ = v_id_3406_;
v___y_3346_ = v___y_3412_;
v___y_3347_ = v_nondep_3414_;
goto v___jp_3334_;
}
}
else
{
uint8_t v_usedOnly_3421_; uint8_t v_zeta_3422_; lean_object* v_eq_x3f_3423_; 
v_usedOnly_3421_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 1);
v_zeta_3422_ = lean_ctor_get_uint8(v_config_3287_, sizeof(void*)*1 + 2);
v_eq_x3f_3423_ = lean_ctor_get(v_config_3287_, 0);
lean_inc(v_eq_x3f_3423_);
lean_dec_ref(v_config_3287_);
lean_inc(v_id_3406_);
v___y_3335_ = v_eq_x3f_3423_;
v___y_3336_ = v_zeta_3422_;
v___y_3337_ = v_usedOnly_3421_;
v___y_3338_ = v_id_3406_;
v___y_3339_ = v___y_3413_;
v___y_3340_ = v___y_3408_;
v___y_3341_ = v___y_3407_;
v___y_3342_ = v___y_3410_;
v___y_3343_ = v___y_3409_;
v___y_3344_ = v___y_3411_;
v___y_3345_ = v_id_3406_;
v___y_3346_ = v___y_3412_;
v___y_3347_ = v___x_3318_;
goto v___jp_3334_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3435_ = lean_unsigned_to_nat(1u);
v___x_3436_ = l_Lean_Syntax_getArg(v___x_3321_, v___x_3435_);
v___x_3437_ = l_Lean_Syntax_matchesNull(v___x_3436_, v___x_3320_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; 
lean_dec(v___x_3321_);
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v___x_3438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3438_;
}
else
{
lean_object* v___x_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; lean_object* v_rhs_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v_xType_x3f_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3439_ = lean_box(v___x_3323_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3440_, 0, v___x_3439_);
v___x_3441_ = l_Lean_Syntax_getArg(v___x_3321_, v___x_3320_);
v___x_3496_ = lean_unsigned_to_nat(2u);
v___x_3497_ = l_Lean_Syntax_getArg(v___x_3321_, v___x_3496_);
v___x_3498_ = l_Lean_Syntax_isNone(v___x_3497_);
if (v___x_3498_ == 0)
{
uint8_t v___x_3499_; 
lean_inc(v___x_3497_);
v___x_3499_ = l_Lean_Syntax_matchesNull(v___x_3497_, v___x_3435_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___x_3497_);
lean_dec(v___x_3441_);
lean_dec_ref(v___f_3440_);
lean_dec(v___x_3321_);
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v___x_3500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3501_ = l_Lean_Syntax_getArg(v___x_3497_, v___x_3320_);
lean_dec(v___x_3497_);
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3501_);
v___x_3503_ = l_Lean_Syntax_isOfKind(v___x_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_dec(v___x_3501_);
lean_dec(v___x_3441_);
lean_dec_ref(v___f_3440_);
lean_dec(v___x_3321_);
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v___x_3504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3504_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = l_Lean_Syntax_getArg(v___x_3501_, v___x_3435_);
lean_dec(v___x_3501_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 1);
lean_ctor_set(v___x_3312_, 0, v___x_3505_);
v___x_3507_ = v___x_3312_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v_xType_x3f_3462_ = v___x_3507_;
v___y_3463_ = v_a_3292_;
v___y_3464_ = v_a_3293_;
v___y_3465_ = v_a_3294_;
v___y_3466_ = v_a_3295_;
v___y_3467_ = v_a_3296_;
v___y_3468_ = v_a_3297_;
v___y_3469_ = v_a_3298_;
goto v___jp_3461_;
}
}
}
}
else
{
lean_object* v___x_3509_; 
lean_dec(v___x_3497_);
lean_del_object(v___x_3312_);
v___x_3509_ = lean_box(0);
v_xType_x3f_3462_ = v___x_3509_;
v___y_3463_ = v_a_3292_;
v___y_3464_ = v_a_3293_;
v___y_3465_ = v_a_3294_;
v___y_3466_ = v_a_3295_;
v___y_3467_ = v_a_3296_;
v___y_3468_ = v_a_3297_;
v___y_3469_ = v_a_3298_;
goto v___jp_3461_;
}
v___jp_3442_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3451_ = lean_box(v___x_3323_);
v___x_3452_ = lean_box(v___x_3318_);
lean_inc(v___x_3441_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3453_, 0, v_rhs_3443_);
lean_closure_set(v___f_3453_, 1, v___x_3451_);
lean_closure_set(v___f_3453_, 2, v_config_3287_);
lean_closure_set(v___f_3453_, 3, v_a_3310_);
lean_closure_set(v___f_3453_, 4, v___x_3452_);
lean_closure_set(v___f_3453_, 5, v___x_3314_);
lean_closure_set(v___f_3453_, 6, v___x_3315_);
lean_closure_set(v___f_3453_, 7, v___x_3316_);
lean_closure_set(v___f_3453_, 8, v___f_3440_);
lean_closure_set(v___f_3453_, 9, v___x_3441_);
v___x_3454_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3454_, 0, v_a_3305_);
v___x_3455_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3455_, 0, v_letOrReassign_3288_);
lean_closure_set(v___x_3455_, 1, v_a_3302_);
lean_closure_set(v___x_3455_, 2, v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3457_ = l_Lean_MessageData_ofSyntax(v___x_3441_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_box(0);
v___x_3460_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3458_, v___x_3455_, v___f_3453_, v___x_3459_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3460_;
}
v___jp_3461_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(4u);
v___x_3471_ = l_Lean_Syntax_getArg(v___x_3321_, v___x_3470_);
lean_dec(v___x_3321_);
if (lean_obj_tag(v_xType_x3f_3462_) == 0)
{
v_rhs_3443_ = v___x_3471_;
v___y_3444_ = v___y_3463_;
v___y_3445_ = v___y_3464_;
v___y_3446_ = v___y_3465_;
v___y_3447_ = v___y_3466_;
v___y_3448_ = v___y_3467_;
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3469_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3472_; lean_object* v_ref_3473_; lean_object* v_quotContext_3474_; lean_object* v_currMacroScope_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_val_3472_ = lean_ctor_get(v_xType_x3f_3462_, 0);
lean_inc(v_val_3472_);
lean_dec_ref_known(v_xType_x3f_3462_, 1);
v_ref_3473_ = lean_ctor_get(v___y_3468_, 5);
v_quotContext_3474_ = lean_ctor_get(v___y_3468_, 10);
v_currMacroScope_3475_ = lean_ctor_get(v___y_3468_, 11);
v___x_3476_ = l_Lean_SourceInfo_fromRef(v_ref_3473_, v___x_3323_);
v___x_3477_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3478_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3479_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3476_, 7);
v___x_3480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3476_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3482_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3483_ = lean_box(0);
lean_inc(v_currMacroScope_3475_);
lean_inc(v_quotContext_3474_);
v___x_3484_ = l_Lean_addMacroScope(v_quotContext_3474_, v___x_3483_, v_currMacroScope_3475_);
v___x_3485_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3476_);
lean_ctor_set(v___x_3486_, 1, v___x_3482_);
lean_ctor_set(v___x_3486_, 2, v___x_3484_);
lean_ctor_set(v___x_3486_, 3, v___x_3485_);
v___x_3487_ = l_Lean_Syntax_node1(v___x_3476_, v___x_3481_, v___x_3486_);
v___x_3488_ = l_Lean_Syntax_node2(v___x_3476_, v___x_3478_, v___x_3480_, v___x_3487_);
v___x_3489_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3476_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3492_ = l_Lean_Syntax_node1(v___x_3476_, v___x_3491_, v_val_3472_);
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3476_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_Syntax_node5(v___x_3476_, v___x_3477_, v___x_3488_, v___x_3471_, v___x_3490_, v___x_3492_, v___x_3494_);
v_rhs_3443_ = v___x_3495_;
v___y_3444_ = v___y_3463_;
v___y_3445_ = v___y_3464_;
v___y_3446_ = v___y_3465_;
v___y_3447_ = v___y_3466_;
v___y_3448_ = v___y_3467_;
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3469_;
goto v___jp_3442_;
}
}
}
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_del_object(v___x_3312_);
lean_dec(v_a_3310_);
lean_dec(v_a_3302_);
v___x_3510_ = lean_box(v___x_3318_);
lean_inc(v___x_3321_);
v___x_3511_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3511_, 0, v___x_3321_);
lean_closure_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3511_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_ref_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v_ref_3514_ = lean_ctor_get(v_a_3297_, 5);
v___x_3515_ = 0;
v___x_3516_ = l_Lean_SourceInfo_fromRef(v_ref_3514_, v___x_3515_);
v___x_3517_ = l_Lean_Syntax_node1(v___x_3516_, v___x_3317_, v_a_3513_);
lean_inc(v___x_3517_);
v___x_3518_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3518_, 0, v_config_3287_);
lean_closure_set(v___x_3518_, 1, v_letOrReassign_3288_);
lean_closure_set(v___x_3518_, 2, v___x_3517_);
lean_closure_set(v___x_3518_, 3, v_tk_3290_);
lean_closure_set(v___x_3518_, 4, v_a_3305_);
v___x_3519_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3321_, v___x_3517_, v___x_3518_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
return v___x_3519_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v___x_3321_);
lean_dec(v_a_3305_);
lean_dec(v_tk_3290_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3520_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3512_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3512_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3307_);
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_tk_3290_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
return v___x_3309_;
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3302_);
lean_dec(v_tk_3290_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3529_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3306_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3306_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v_a_3302_);
lean_dec(v_tk_3290_);
lean_dec(v_decl_3289_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3537_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3304_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3304_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_a_3302_);
lean_dec_ref(v_dec_3291_);
lean_dec(v_tk_3290_);
lean_dec(v_decl_3289_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3545_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3303_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3303_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v_dec_3291_);
lean_dec(v_tk_3290_);
lean_dec(v_decl_3289_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3553_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3301_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3301_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_dec_3291_);
lean_dec(v_tk_3290_);
lean_dec(v_decl_3289_);
lean_dec(v_letOrReassign_3288_);
lean_dec_ref(v_config_3287_);
v_a_3561_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3300_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3300_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3570_, v_x_3571_, v_x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3574_, lean_object* v_msg_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3574_, v_msg_3575_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3585_, lean_object* v_msg_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3585_, v_msg_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3601_, v___y_3602_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3614_, lean_object* v_beforeStx_3615_, lean_object* v_afterStx_3616_, lean_object* v_x_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3615_, v_afterStx_3616_, v_x_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3627_, lean_object* v_beforeStx_3628_, lean_object* v_afterStx_3629_, lean_object* v_x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3627_, v_beforeStx_3628_, v_afterStx_3629_, v_x_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3640_, lean_object* v_x_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3641_, v___y_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3645_, lean_object* v_x_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3645_, v_x_3646_, v___y_3647_, v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec_ref(v_x_3646_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3650_, lean_object* v_ref_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3651_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3661_, lean_object* v_ref_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3661_, v_ref_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3672_, lean_object* v_x_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3683_, v_x_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3694_, lean_object* v_x_3695_, size_t v_x_3696_, size_t v_x_3697_, lean_object* v_x_3698_, lean_object* v_x_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3695_, v_x_3696_, v_x_3697_, v_x_3698_, v_x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v_x_3704_, lean_object* v_x_3705_, lean_object* v_x_3706_){
_start:
{
size_t v_x_103037__boxed_3707_; size_t v_x_103038__boxed_3708_; lean_object* v_res_3709_; 
v_x_103037__boxed_3707_ = lean_unbox_usize(v_x_3703_);
lean_dec(v_x_3703_);
v_x_103038__boxed_3708_ = lean_unbox_usize(v_x_3704_);
lean_dec(v_x_3704_);
v_res_3709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3701_, v_x_3702_, v_x_103037__boxed_3707_, v_x_103038__boxed_3708_, v_x_3705_, v_x_3706_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3710_, lean_object* v_stx_3711_, lean_object* v_output_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3711_, v_output_3712_, v_x_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3722_, lean_object* v_stx_3723_, lean_object* v_output_3724_, lean_object* v_x_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3722_, v_stx_3723_, v_output_3724_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3734_, lean_object* v_as_x27_3735_, lean_object* v_b_3736_, lean_object* v_a_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3735_, v_b_3736_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3747_, lean_object* v_as_x27_3748_, lean_object* v_b_3749_, lean_object* v_a_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3747_, v_as_x27_3748_, v_b_3749_, v_a_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v_as_x27_3748_);
lean_dec(v_as_3747_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3760_, lean_object* v_ref_3761_, lean_object* v_msg_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3761_, v_msg_3762_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3772_, lean_object* v_ref_3773_, lean_object* v_msg_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3772_, v_ref_3773_, v_msg_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v_ref_3773_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3784_, lean_object* v_n_3785_, lean_object* v_k_3786_, lean_object* v_v_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3785_, v_k_3786_, v_v_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3789_, size_t v_depth_3790_, lean_object* v_keys_3791_, lean_object* v_vals_3792_, lean_object* v_heq_3793_, lean_object* v_i_3794_, lean_object* v_entries_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3790_, v_keys_3791_, v_vals_3792_, v_i_3794_, v_entries_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3797_, lean_object* v_depth_3798_, lean_object* v_keys_3799_, lean_object* v_vals_3800_, lean_object* v_heq_3801_, lean_object* v_i_3802_, lean_object* v_entries_3803_){
_start:
{
size_t v_depth_boxed_3804_; lean_object* v_res_3805_; 
v_depth_boxed_3804_ = lean_unbox_usize(v_depth_3798_);
lean_dec(v_depth_3798_);
v_res_3805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3797_, v_depth_boxed_3804_, v_keys_3799_, v_vals_3800_, v_heq_3801_, v_i_3802_, v_entries_3803_);
lean_dec_ref(v_vals_3800_);
lean_dec_ref(v_keys_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3822_, lean_object* v_x_3823_, lean_object* v_mkInfoTree_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3823_, v_mkInfoTree_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3833_, lean_object* v_x_3834_, lean_object* v_mkInfoTree_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3833_, v_x_3834_, v_mkInfoTree_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3844_, lean_object* v_m_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3845_, v_a_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3848_, lean_object* v_m_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3848_, v_m_3849_, v_a_3850_);
lean_dec(v_a_3850_);
lean_dec_ref(v_m_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3852_, lean_object* v_x_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3853_, v_x_3854_, v_x_3855_, v_x_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3858_, lean_object* v_x_3859_, lean_object* v_x_3860_){
_start:
{
uint8_t v___x_3861_; 
v___x_3861_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3859_, v_x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3862_, lean_object* v_x_3863_, lean_object* v_x_3864_){
_start:
{
uint8_t v_res_3865_; lean_object* v_r_3866_; 
v_res_3865_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3862_, v_x_3863_, v_x_3864_);
lean_dec_ref(v_x_3864_);
lean_dec_ref(v_x_3863_);
v_r_3866_ = lean_box(v_res_3865_);
return v_r_3866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3867_, lean_object* v_m_3868_, lean_object* v_query_3869_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_m_3868_, v_query_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_m_3872_, lean_object* v_query_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3871_, v_m_3872_, v_query_3873_);
lean_dec(v_query_3873_);
lean_dec_ref(v_m_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3875_, lean_object* v_x_3876_, size_t v_x_3877_, lean_object* v_x_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3876_, v_x_3877_, v_x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3880_, lean_object* v_x_3881_, lean_object* v_x_3882_, lean_object* v_x_3883_){
_start:
{
size_t v_x_103204__boxed_3884_; uint8_t v_res_3885_; lean_object* v_r_3886_; 
v_x_103204__boxed_3884_ = lean_unbox_usize(v_x_3882_);
lean_dec(v_x_3882_);
v_res_3885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3880_, v_x_3881_, v_x_103204__boxed_3884_, v_x_3883_);
lean_dec_ref(v_x_3883_);
lean_dec_ref(v_x_3881_);
v_r_3886_ = lean_box(v_res_3885_);
return v_r_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29(lean_object* v_00_u03b2_3887_, lean_object* v_m_3888_, lean_object* v_query_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___redArg(v_m_3888_, v_query_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29___boxed(lean_object* v_00_u03b2_3891_, lean_object* v_m_3892_, lean_object* v_query_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29(v_00_u03b2_3891_, v_m_3892_, v_query_3893_);
lean_dec(v_query_3893_);
lean_dec_ref(v_m_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3895_, lean_object* v_keys_3896_, lean_object* v_vals_3897_, lean_object* v_heq_3898_, lean_object* v_i_3899_, lean_object* v_k_3900_){
_start:
{
uint8_t v___x_3901_; 
v___x_3901_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3896_, v_i_3899_, v_k_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3902_, lean_object* v_keys_3903_, lean_object* v_vals_3904_, lean_object* v_heq_3905_, lean_object* v_i_3906_, lean_object* v_k_3907_){
_start:
{
uint8_t v_res_3908_; lean_object* v_r_3909_; 
v_res_3908_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3902_, v_keys_3903_, v_vals_3904_, v_heq_3905_, v_i_3906_, v_k_3907_);
lean_dec_ref(v_k_3907_);
lean_dec_ref(v_vals_3904_);
lean_dec_ref(v_keys_3903_);
v_r_3909_ = lean_box(v_res_3908_);
return v_r_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31(lean_object* v_00_u03b2_3910_, lean_object* v_m_3911_, lean_object* v_query_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_, lean_object* v_x_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___redArg(v_m_3911_, v_query_3912_, v_x_3913_, v_x_3914_, v_x_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31___boxed(lean_object* v_00_u03b2_3918_, lean_object* v_m_3919_, lean_object* v_query_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24_spec__29_spec__31(v_00_u03b2_3918_, v_m_3919_, v_query_3920_, v_x_3921_, v_x_3922_, v_x_3923_, v_x_3924_);
lean_dec(v_query_3920_);
lean_dec_ref(v_m_3919_);
return v_res_3925_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3935_, lean_object* v_otherwise_x3f_3936_, uint8_t v___x_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v___x_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v_dec_3943_, uint8_t v___x_3944_, lean_object* v___y_3945_, lean_object* v___x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; uint8_t v___y_3978_; 
switch(lean_obj_tag(v_letOrReassign_3935_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3936_) == 1)
{
lean_object* v_mutTk_x3f_3989_; lean_object* v_val_3990_; lean_object* v_ref_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4021_; 
v_mutTk_x3f_3989_ = lean_ctor_get(v_letOrReassign_3935_, 0);
v_val_3990_ = lean_ctor_get(v_otherwise_x3f_3936_, 0);
lean_inc(v_val_3990_);
lean_dec_ref_known(v_otherwise_x3f_3936_, 1);
v_ref_3991_ = lean_ctor_get(v___y_3952_, 5);
v___x_3992_ = l_Lean_SourceInfo_fromRef(v_ref_3991_, v___x_3937_);
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3940_);
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
v___x_3994_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_3993_);
v___x_3995_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3992_);
v___x_3996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3992_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3998_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3989_) == 1)
{
lean_object* v_val_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_val_4036_ = lean_ctor_get(v_mutTk_x3f_3989_, 0);
v___x_4037_ = l_Lean_SourceInfo_fromRef(v_val_4036_, v___x_3944_);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Array_mkArray1___redArg(v___x_4039_);
v___y_4021_ = v___x_4040_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_mk_empty_array_with_capacity(v___x_3946_);
v___y_4021_ = v___x_4041_;
goto v___jp_4020_;
}
v___jp_3999_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4005_ = l_Array_append___redArg(v___x_3998_, v___y_4004_);
lean_dec_ref(v___y_4004_);
lean_inc(v___x_3992_);
v___x_4006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4006_, 0, v___x_3992_);
lean_ctor_set(v___x_4006_, 1, v___x_3997_);
lean_ctor_set(v___x_4006_, 2, v___x_4005_);
v___x_4007_ = lean_unsigned_to_nat(9u);
v___x_4008_ = lean_mk_empty_array_with_capacity(v___x_4007_);
v___x_4009_ = lean_array_push(v___x_4008_, v___x_3996_);
v___x_4010_ = lean_array_push(v___x_4009_, v___y_4001_);
v___x_4011_ = lean_array_push(v___x_4010_, v___y_4000_);
v___x_4012_ = lean_array_push(v___x_4011_, v___x_3941_);
v___x_4013_ = lean_array_push(v___x_4012_, v___y_4003_);
v___x_4014_ = lean_array_push(v___x_4013_, v___x_3942_);
v___x_4015_ = lean_array_push(v___x_4014_, v___y_4002_);
v___x_4016_ = lean_array_push(v___x_4015_, v_val_3990_);
v___x_4017_ = lean_array_push(v___x_4016_, v___x_4006_);
v___x_4018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4018_, 0, v___x_3992_);
lean_ctor_set(v___x_4018_, 1, v___x_3994_);
lean_ctor_set(v___x_4018_, 2, v___x_4017_);
v___x_4019_ = l_Lean_Elab_Do_elabDoElem(v___x_4018_, v_dec_3943_, v___x_3944_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_4019_;
}
v___jp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4022_ = l_Array_append___redArg(v___x_3998_, v___y_4021_);
lean_dec_ref(v___y_4021_);
lean_inc_n(v___x_3992_, 5);
v___x_4023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4023_, 0, v___x_3992_);
lean_ctor_set(v___x_4023_, 1, v___x_3997_);
lean_ctor_set(v___x_4023_, 2, v___x_4022_);
v___x_4024_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4025_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4024_);
v___x_4026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4026_, 0, v___x_3992_);
lean_ctor_set(v___x_4026_, 1, v___x_3997_);
lean_ctor_set(v___x_4026_, 2, v___x_3998_);
v___x_4027_ = l_Lean_Syntax_node1(v___x_3992_, v___x_4025_, v___x_4026_);
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_3992_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_3992_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
if (lean_obj_tag(v___y_3945_) == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_mk_empty_array_with_capacity(v___x_3946_);
v___y_4000_ = v___x_4027_;
v___y_4001_ = v___x_4023_;
v___y_4002_ = v___x_4031_;
v___y_4003_ = v___x_4029_;
v___y_4004_ = v___x_4032_;
goto v___jp_3999_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v_val_4033_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v___y_3945_, 1);
v___x_4034_ = lean_mk_empty_array_with_capacity(v___x_3946_);
v___x_4035_ = lean_array_push(v___x_4034_, v_val_4033_);
v___y_4000_ = v___x_4027_;
v___y_4001_ = v___x_4023_;
v___y_4002_ = v___x_4031_;
v___y_4003_ = v___x_4029_;
v___y_4004_ = v___x_4035_;
goto v___jp_3999_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4042_; lean_object* v_ref_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___y_4052_; 
lean_dec(v___y_3945_);
lean_dec(v_otherwise_x3f_3936_);
v_mutTk_x3f_4042_ = lean_ctor_get(v_letOrReassign_3935_, 0);
v_ref_4043_ = lean_ctor_get(v___y_3952_, 5);
v___x_4044_ = l_Lean_SourceInfo_fromRef(v_ref_4043_, v___x_3937_);
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3940_);
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
v___x_4046_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4045_);
v___x_4047_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4044_);
v___x_4048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4044_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4050_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4042_) == 1)
{
lean_object* v_val_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_val_4069_ = lean_ctor_get(v_mutTk_x3f_4042_, 0);
v___x_4070_ = l_Lean_SourceInfo_fromRef(v_val_4069_, v___x_3944_);
v___x_4071_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Array_mkArray1___redArg(v___x_4072_);
v___y_4052_ = v___x_4073_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_mk_empty_array_with_capacity(v___x_3946_);
v___y_4052_ = v___x_4074_;
goto v___jp_4051_;
}
v___jp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4053_ = l_Array_append___redArg(v___x_4050_, v___y_4052_);
lean_dec_ref(v___y_4052_);
lean_inc_n(v___x_4044_, 6);
v___x_4054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4044_);
lean_ctor_set(v___x_4054_, 1, v___x_4049_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
v___x_4055_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3940_, 2);
lean_inc_ref_n(v___x_3939_, 2);
lean_inc_ref_n(v___x_3938_, 2);
v___x_4056_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4044_);
lean_ctor_set(v___x_4057_, 1, v___x_4049_);
lean_ctor_set(v___x_4057_, 2, v___x_4050_);
lean_inc_ref_n(v___x_4057_, 2);
v___x_4058_ = l_Lean_Syntax_node1(v___x_4044_, v___x_4056_, v___x_4057_);
v___x_4059_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4060_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4059_);
v___x_4061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4062_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4061_);
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4044_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = l_Lean_Syntax_node5(v___x_4044_, v___x_4062_, v___x_3941_, v___x_4057_, v___x_4057_, v___x_4064_, v___x_3942_);
v___x_4066_ = l_Lean_Syntax_node1(v___x_4044_, v___x_4060_, v___x_4065_);
v___x_4067_ = l_Lean_Syntax_node4(v___x_4044_, v___x_4046_, v___x_4048_, v___x_4054_, v___x_4058_, v___x_4066_);
v___x_4068_ = l_Lean_Elab_Do_elabDoElem(v___x_4067_, v_dec_3943_, v___x_3944_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_4068_;
}
}
}
case 1:
{
lean_dec(v___y_3945_);
if (lean_obj_tag(v_otherwise_x3f_3936_) == 1)
{
lean_object* v___x_4075_; 
lean_dec_ref_known(v_otherwise_x3f_3936_, 1);
lean_dec_ref(v_dec_3943_);
lean_dec(v___x_3942_);
lean_dec(v___x_3941_);
lean_dec_ref(v___x_3940_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
v___x_4075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4075_;
}
else
{
lean_object* v_ref_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v_otherwise_x3f_3936_);
v_ref_4076_ = lean_ctor_get(v___y_3952_, 5);
v___x_4077_ = l_Lean_SourceInfo_fromRef(v_ref_4076_, v___x_3937_);
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3940_, 3);
lean_inc_ref_n(v___x_3939_, 3);
lean_inc_ref_n(v___x_3938_, 3);
v___x_4079_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4078_);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4077_, 6);
v___x_4081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4077_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4083_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4082_);
v___x_4084_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4085_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4077_);
lean_ctor_set(v___x_4086_, 1, v___x_4084_);
lean_ctor_set(v___x_4086_, 2, v___x_4085_);
lean_inc_ref_n(v___x_4086_, 2);
v___x_4087_ = l_Lean_Syntax_node1(v___x_4077_, v___x_4083_, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4089_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4088_);
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4091_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_4090_);
v___x_4092_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4077_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l_Lean_Syntax_node5(v___x_4077_, v___x_4091_, v___x_3941_, v___x_4086_, v___x_4086_, v___x_4093_, v___x_3942_);
v___x_4095_ = l_Lean_Syntax_node1(v___x_4077_, v___x_4089_, v___x_4094_);
v___x_4096_ = l_Lean_Syntax_node3(v___x_4077_, v___x_4079_, v___x_4081_, v___x_4087_, v___x_4095_);
v___x_4097_ = l_Lean_Elab_Do_elabDoElem(v___x_4096_, v_dec_3943_, v___x_3944_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_4097_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3936_);
if (lean_obj_tag(v___y_3945_) == 0)
{
v___y_3978_ = v___x_3944_;
goto v___jp_3977_;
}
else
{
lean_dec_ref_known(v___y_3945_, 1);
v___y_3978_ = v___x_3937_;
goto v___jp_3977_;
}
}
}
v___jp_3955_:
{
lean_object* v_ref_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_ref_3963_ = lean_ctor_get(v___y_3961_, 5);
v___x_3964_ = l_Lean_SourceInfo_fromRef(v_ref_3963_, v___x_3937_);
v___x_3965_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3940_);
lean_inc_ref(v___x_3939_);
lean_inc_ref(v___x_3938_);
v___x_3966_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3968_ = l_Lean_Name_mkStr4(v___x_3938_, v___x_3939_, v___x_3940_, v___x_3967_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3970_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3964_, 3);
v___x_3971_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3964_);
lean_ctor_set(v___x_3971_, 1, v___x_3969_);
lean_ctor_set(v___x_3971_, 2, v___x_3970_);
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3964_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
lean_inc_ref(v___x_3971_);
v___x_3974_ = l_Lean_Syntax_node5(v___x_3964_, v___x_3968_, v___x_3941_, v___x_3971_, v___x_3971_, v___x_3973_, v___x_3942_);
v___x_3975_ = l_Lean_Syntax_node1(v___x_3964_, v___x_3966_, v___x_3974_);
v___x_3976_ = l_Lean_Elab_Do_elabDoElem(v___x_3975_, v_dec_3943_, v___x_3944_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3976_;
}
v___jp_3977_:
{
if (v___y_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v_dec_3943_);
lean_dec(v___x_3942_);
lean_dec(v___x_3941_);
lean_dec_ref(v___x_3940_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
v___x_3979_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3980_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_3979_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
v___y_3956_ = v___y_3947_;
v___y_3957_ = v___y_3948_;
v___y_3958_ = v___y_3949_;
v___y_3959_ = v___y_3950_;
v___y_3960_ = v___y_3951_;
v___y_3961_ = v___y_3952_;
v___y_3962_ = v___y_3953_;
goto v___jp_3955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4098_ = _args[0];
lean_object* v_otherwise_x3f_4099_ = _args[1];
lean_object* v___x_4100_ = _args[2];
lean_object* v___x_4101_ = _args[3];
lean_object* v___x_4102_ = _args[4];
lean_object* v___x_4103_ = _args[5];
lean_object* v___x_4104_ = _args[6];
lean_object* v___x_4105_ = _args[7];
lean_object* v_dec_4106_ = _args[8];
lean_object* v___x_4107_ = _args[9];
lean_object* v___y_4108_ = _args[10];
lean_object* v___x_4109_ = _args[11];
lean_object* v___y_4110_ = _args[12];
lean_object* v___y_4111_ = _args[13];
lean_object* v___y_4112_ = _args[14];
lean_object* v___y_4113_ = _args[15];
lean_object* v___y_4114_ = _args[16];
lean_object* v___y_4115_ = _args[17];
lean_object* v___y_4116_ = _args[18];
lean_object* v___y_4117_ = _args[19];
_start:
{
uint8_t v___x_39001__boxed_4118_; uint8_t v___x_39007__boxed_4119_; lean_object* v_res_4120_; 
v___x_39001__boxed_4118_ = lean_unbox(v___x_4100_);
v___x_39007__boxed_4119_ = lean_unbox(v___x_4107_);
v_res_4120_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4098_, v_otherwise_x3f_4099_, v___x_39001__boxed_4118_, v___x_4101_, v___x_4102_, v___x_4103_, v___x_4104_, v___x_4105_, v_dec_4106_, v___x_39007__boxed_4119_, v___y_4108_, v___x_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___x_4109_);
lean_dec(v_letOrReassign_4098_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4121_, lean_object* v_otherwise_x3f_4122_, uint8_t v___x_4123_, lean_object* v___x_4124_, lean_object* v___x_4125_, lean_object* v___x_4126_, lean_object* v___x_4127_, lean_object* v___x_4128_, lean_object* v_dec_4129_, uint8_t v___x_4130_, lean_object* v___y_4131_, lean_object* v___x_4132_, uint8_t v___x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; uint8_t v___y_4165_; 
switch(lean_obj_tag(v_letOrReassign_4121_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4122_) == 1)
{
lean_object* v_mutTk_x3f_4176_; lean_object* v_val_4177_; lean_object* v_ref_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4208_; 
v_mutTk_x3f_4176_ = lean_ctor_get(v_letOrReassign_4121_, 0);
v_val_4177_ = lean_ctor_get(v_otherwise_x3f_4122_, 0);
lean_inc(v_val_4177_);
lean_dec_ref_known(v_otherwise_x3f_4122_, 1);
v_ref_4178_ = lean_ctor_get(v___y_4139_, 5);
v___x_4179_ = l_Lean_SourceInfo_fromRef(v_ref_4178_, v___x_4123_);
v___x_4180_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4126_);
lean_inc_ref(v___x_4125_);
lean_inc_ref(v___x_4124_);
v___x_4181_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4179_);
v___x_4183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4179_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v___x_4184_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4185_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4176_) == 1)
{
lean_object* v_val_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_val_4223_ = lean_ctor_get(v_mutTk_x3f_4176_, 0);
v___x_4224_ = l_Lean_SourceInfo_fromRef(v_val_4223_, v___x_4130_);
v___x_4225_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4224_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l_Array_mkArray1___redArg(v___x_4226_);
v___y_4208_ = v___x_4227_;
goto v___jp_4207_;
}
else
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_mk_empty_array_with_capacity(v___x_4132_);
v___y_4208_ = v___x_4228_;
goto v___jp_4207_;
}
v___jp_4186_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4192_ = l_Array_append___redArg(v___x_4185_, v___y_4191_);
lean_dec_ref(v___y_4191_);
lean_inc(v___x_4179_);
v___x_4193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4179_);
lean_ctor_set(v___x_4193_, 1, v___x_4184_);
lean_ctor_set(v___x_4193_, 2, v___x_4192_);
v___x_4194_ = lean_unsigned_to_nat(9u);
v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4194_);
v___x_4196_ = lean_array_push(v___x_4195_, v___x_4183_);
v___x_4197_ = lean_array_push(v___x_4196_, v___y_4190_);
v___x_4198_ = lean_array_push(v___x_4197_, v___y_4189_);
v___x_4199_ = lean_array_push(v___x_4198_, v___x_4127_);
v___x_4200_ = lean_array_push(v___x_4199_, v___y_4187_);
v___x_4201_ = lean_array_push(v___x_4200_, v___x_4128_);
v___x_4202_ = lean_array_push(v___x_4201_, v___y_4188_);
v___x_4203_ = lean_array_push(v___x_4202_, v_val_4177_);
v___x_4204_ = lean_array_push(v___x_4203_, v___x_4193_);
v___x_4205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4179_);
lean_ctor_set(v___x_4205_, 1, v___x_4181_);
lean_ctor_set(v___x_4205_, 2, v___x_4204_);
v___x_4206_ = l_Lean_Elab_Do_elabDoElem(v___x_4205_, v_dec_4129_, v___x_4130_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4206_;
}
v___jp_4207_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4209_ = l_Array_append___redArg(v___x_4185_, v___y_4208_);
lean_dec_ref(v___y_4208_);
lean_inc_n(v___x_4179_, 5);
v___x_4210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4179_);
lean_ctor_set(v___x_4210_, 1, v___x_4184_);
lean_ctor_set(v___x_4210_, 2, v___x_4209_);
v___x_4211_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4212_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4211_);
v___x_4213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4179_);
lean_ctor_set(v___x_4213_, 1, v___x_4184_);
lean_ctor_set(v___x_4213_, 2, v___x_4185_);
v___x_4214_ = l_Lean_Syntax_node1(v___x_4179_, v___x_4212_, v___x_4213_);
v___x_4215_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4179_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4179_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
if (lean_obj_tag(v___y_4131_) == 0)
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_mk_empty_array_with_capacity(v___x_4132_);
v___y_4187_ = v___x_4216_;
v___y_4188_ = v___x_4218_;
v___y_4189_ = v___x_4214_;
v___y_4190_ = v___x_4210_;
v___y_4191_ = v___x_4219_;
goto v___jp_4186_;
}
else
{
lean_object* v_val_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_val_4220_ = lean_ctor_get(v___y_4131_, 0);
lean_inc(v_val_4220_);
lean_dec_ref_known(v___y_4131_, 1);
v___x_4221_ = lean_mk_empty_array_with_capacity(v___x_4132_);
v___x_4222_ = lean_array_push(v___x_4221_, v_val_4220_);
v___y_4187_ = v___x_4216_;
v___y_4188_ = v___x_4218_;
v___y_4189_ = v___x_4214_;
v___y_4190_ = v___x_4210_;
v___y_4191_ = v___x_4222_;
goto v___jp_4186_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4229_; lean_object* v_ref_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___y_4239_; 
lean_dec(v___y_4131_);
lean_dec(v_otherwise_x3f_4122_);
v_mutTk_x3f_4229_ = lean_ctor_get(v_letOrReassign_4121_, 0);
v_ref_4230_ = lean_ctor_get(v___y_4139_, 5);
v___x_4231_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4123_);
v___x_4232_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4126_);
lean_inc_ref(v___x_4125_);
lean_inc_ref(v___x_4124_);
v___x_4233_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4232_);
v___x_4234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4231_);
v___x_4235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4231_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4237_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4229_) == 1)
{
lean_object* v_val_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_val_4256_ = lean_ctor_get(v_mutTk_x3f_4229_, 0);
v___x_4257_ = l_Lean_SourceInfo_fromRef(v_val_4256_, v___x_4130_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Array_mkArray1___redArg(v___x_4259_);
v___y_4239_ = v___x_4260_;
goto v___jp_4238_;
}
else
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_mk_empty_array_with_capacity(v___x_4132_);
v___y_4239_ = v___x_4261_;
goto v___jp_4238_;
}
v___jp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4240_ = l_Array_append___redArg(v___x_4237_, v___y_4239_);
lean_dec_ref(v___y_4239_);
lean_inc_n(v___x_4231_, 6);
v___x_4241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4231_);
lean_ctor_set(v___x_4241_, 1, v___x_4236_);
lean_ctor_set(v___x_4241_, 2, v___x_4240_);
v___x_4242_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4126_, 2);
lean_inc_ref_n(v___x_4125_, 2);
lean_inc_ref_n(v___x_4124_, 2);
v___x_4243_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4231_);
lean_ctor_set(v___x_4244_, 1, v___x_4236_);
lean_ctor_set(v___x_4244_, 2, v___x_4237_);
lean_inc_ref_n(v___x_4244_, 2);
v___x_4245_ = l_Lean_Syntax_node1(v___x_4231_, v___x_4243_, v___x_4244_);
v___x_4246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4247_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4246_);
v___x_4248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4249_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4248_);
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4231_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = l_Lean_Syntax_node5(v___x_4231_, v___x_4249_, v___x_4127_, v___x_4244_, v___x_4244_, v___x_4251_, v___x_4128_);
v___x_4253_ = l_Lean_Syntax_node1(v___x_4231_, v___x_4247_, v___x_4252_);
v___x_4254_ = l_Lean_Syntax_node4(v___x_4231_, v___x_4233_, v___x_4235_, v___x_4241_, v___x_4245_, v___x_4253_);
v___x_4255_ = l_Lean_Elab_Do_elabDoElem(v___x_4254_, v_dec_4129_, v___x_4130_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4255_;
}
}
}
case 1:
{
lean_dec(v___y_4131_);
if (lean_obj_tag(v_otherwise_x3f_4122_) == 1)
{
lean_object* v___x_4262_; 
lean_dec_ref_known(v_otherwise_x3f_4122_, 1);
lean_dec_ref(v_dec_4129_);
lean_dec(v___x_4128_);
lean_dec(v___x_4127_);
lean_dec_ref(v___x_4126_);
lean_dec_ref(v___x_4125_);
lean_dec_ref(v___x_4124_);
v___x_4262_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4262_;
}
else
{
lean_object* v_ref_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
lean_dec(v_otherwise_x3f_4122_);
v_ref_4263_ = lean_ctor_get(v___y_4139_, 5);
v___x_4264_ = l_Lean_SourceInfo_fromRef(v_ref_4263_, v___x_4123_);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4126_, 3);
lean_inc_ref_n(v___x_4125_, 3);
lean_inc_ref_n(v___x_4124_, 3);
v___x_4266_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4265_);
v___x_4267_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4264_, 6);
v___x_4268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4264_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4270_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4269_);
v___x_4271_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4272_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4264_);
lean_ctor_set(v___x_4273_, 1, v___x_4271_);
lean_ctor_set(v___x_4273_, 2, v___x_4272_);
lean_inc_ref_n(v___x_4273_, 2);
v___x_4274_ = l_Lean_Syntax_node1(v___x_4264_, v___x_4270_, v___x_4273_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4276_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4275_);
v___x_4277_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4278_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4277_);
v___x_4279_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4264_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l_Lean_Syntax_node5(v___x_4264_, v___x_4278_, v___x_4127_, v___x_4273_, v___x_4273_, v___x_4280_, v___x_4128_);
v___x_4282_ = l_Lean_Syntax_node1(v___x_4264_, v___x_4276_, v___x_4281_);
v___x_4283_ = l_Lean_Syntax_node3(v___x_4264_, v___x_4266_, v___x_4268_, v___x_4274_, v___x_4282_);
v___x_4284_ = l_Lean_Elab_Do_elabDoElem(v___x_4283_, v_dec_4129_, v___x_4130_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4284_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4122_);
if (lean_obj_tag(v___y_4131_) == 0)
{
v___y_4165_ = v___x_4133_;
goto v___jp_4164_;
}
else
{
lean_dec_ref_known(v___y_4131_, 1);
v___y_4165_ = v___x_4123_;
goto v___jp_4164_;
}
}
}
v___jp_4142_:
{
lean_object* v_ref_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_ref_4150_ = lean_ctor_get(v___y_4148_, 5);
v___x_4151_ = l_Lean_SourceInfo_fromRef(v_ref_4150_, v___x_4123_);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4126_);
lean_inc_ref(v___x_4125_);
lean_inc_ref(v___x_4124_);
v___x_4153_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4155_ = l_Lean_Name_mkStr4(v___x_4124_, v___x_4125_, v___x_4126_, v___x_4154_);
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4157_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4151_, 3);
v___x_4158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4151_);
lean_ctor_set(v___x_4158_, 1, v___x_4156_);
lean_ctor_set(v___x_4158_, 2, v___x_4157_);
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4151_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
lean_inc_ref(v___x_4158_);
v___x_4161_ = l_Lean_Syntax_node5(v___x_4151_, v___x_4155_, v___x_4127_, v___x_4158_, v___x_4158_, v___x_4160_, v___x_4128_);
v___x_4162_ = l_Lean_Syntax_node1(v___x_4151_, v___x_4153_, v___x_4161_);
v___x_4163_ = l_Lean_Elab_Do_elabDoElem(v___x_4162_, v_dec_4129_, v___x_4130_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4163_;
}
v___jp_4164_:
{
if (v___y_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec_ref(v_dec_4129_);
lean_dec(v___x_4128_);
lean_dec(v___x_4127_);
lean_dec_ref(v___x_4126_);
lean_dec_ref(v___x_4125_);
lean_dec_ref(v___x_4124_);
v___x_4166_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4167_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4166_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
else
{
v___y_4143_ = v___y_4134_;
v___y_4144_ = v___y_4135_;
v___y_4145_ = v___y_4136_;
v___y_4146_ = v___y_4137_;
v___y_4147_ = v___y_4138_;
v___y_4148_ = v___y_4139_;
v___y_4149_ = v___y_4140_;
goto v___jp_4142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4285_ = _args[0];
lean_object* v_otherwise_x3f_4286_ = _args[1];
lean_object* v___x_4287_ = _args[2];
lean_object* v___x_4288_ = _args[3];
lean_object* v___x_4289_ = _args[4];
lean_object* v___x_4290_ = _args[5];
lean_object* v___x_4291_ = _args[6];
lean_object* v___x_4292_ = _args[7];
lean_object* v_dec_4293_ = _args[8];
lean_object* v___x_4294_ = _args[9];
lean_object* v___y_4295_ = _args[10];
lean_object* v___x_4296_ = _args[11];
lean_object* v___x_4297_ = _args[12];
lean_object* v___y_4298_ = _args[13];
lean_object* v___y_4299_ = _args[14];
lean_object* v___y_4300_ = _args[15];
lean_object* v___y_4301_ = _args[16];
lean_object* v___y_4302_ = _args[17];
lean_object* v___y_4303_ = _args[18];
lean_object* v___y_4304_ = _args[19];
lean_object* v___y_4305_ = _args[20];
_start:
{
uint8_t v___x_39383__boxed_4306_; uint8_t v___x_39389__boxed_4307_; uint8_t v___x_39392__boxed_4308_; lean_object* v_res_4309_; 
v___x_39383__boxed_4306_ = lean_unbox(v___x_4287_);
v___x_39389__boxed_4307_ = lean_unbox(v___x_4294_);
v___x_39392__boxed_4308_ = lean_unbox(v___x_4297_);
v_res_4309_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4285_, v_otherwise_x3f_4286_, v___x_39383__boxed_4306_, v___x_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___x_4292_, v_dec_4293_, v___x_39389__boxed_4307_, v___y_4295_, v___x_4296_, v___x_39392__boxed_4308_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___x_4296_);
lean_dec(v_letOrReassign_4285_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4330_, lean_object* v_stx_4331_, lean_object* v_tk_4332_, lean_object* v_dec_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4342_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4343_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4344_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4345_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4331_);
v___x_4346_ = l_Lean_Syntax_isOfKind(v_stx_4331_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4331_);
v___x_4348_ = l_Lean_Syntax_isOfKind(v_stx_4331_, v___x_4347_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4349_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4349_;
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; 
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4350_);
v___x_4352_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4351_);
v___x_4353_ = l_Lean_Syntax_isOfKind(v___x_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4439_; lean_object* v_patType_x3f_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4439_ = lean_unsigned_to_nat(1u);
v___x_4470_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4439_);
v___x_4471_ = l_Lean_Syntax_isNone(v___x_4470_);
if (v___x_4471_ == 0)
{
uint8_t v___x_4472_; 
lean_inc(v___x_4470_);
v___x_4472_ = l_Lean_Syntax_matchesNull(v___x_4470_, v___x_4439_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; 
lean_dec(v___x_4470_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4473_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; 
v___x_4474_ = l_Lean_Syntax_getArg(v___x_4470_, v___x_4350_);
lean_dec(v___x_4470_);
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4474_);
v___x_4476_ = l_Lean_Syntax_isOfKind(v___x_4474_, v___x_4475_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; 
lean_dec(v___x_4474_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4477_;
}
else
{
lean_object* v_patType_x3f_4478_; lean_object* v___x_4479_; 
v_patType_x3f_4478_ = l_Lean_Syntax_getArg(v___x_4474_, v___x_4439_);
lean_dec(v___x_4474_);
v___x_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4479_, 0, v_patType_x3f_4478_);
v_patType_x3f_4441_ = v___x_4479_;
v___y_4442_ = v_a_4334_;
v___y_4443_ = v_a_4335_;
v___y_4444_ = v_a_4336_;
v___y_4445_ = v_a_4337_;
v___y_4446_ = v_a_4338_;
v___y_4447_ = v_a_4339_;
v___y_4448_ = v_a_4340_;
goto v___jp_4440_;
}
}
}
else
{
lean_object* v___x_4480_; 
lean_dec(v___x_4470_);
v___x_4480_ = lean_box(0);
v_patType_x3f_4441_ = v___x_4480_;
v___y_4442_ = v_a_4334_;
v___y_4443_ = v_a_4335_;
v___y_4444_ = v_a_4336_;
v___y_4445_ = v_a_4337_;
v___y_4446_ = v_a_4338_;
v___y_4447_ = v_a_4339_;
v___y_4448_ = v_a_4340_;
goto v___jp_4440_;
}
v___jp_4440_:
{
lean_object* v___x_4449_; lean_object* v_rhs_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4449_ = lean_unsigned_to_nat(3u);
v_rhs_4450_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4449_);
v___x_4451_ = lean_unsigned_to_nat(4u);
v___x_4452_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4451_);
lean_dec(v_stx_4331_);
v___x_4453_ = l_Lean_Syntax_isNone(v___x_4452_);
if (v___x_4453_ == 0)
{
uint8_t v___x_4454_; 
lean_inc(v___x_4452_);
v___x_4454_ = l_Lean_Syntax_matchesNull(v___x_4452_, v___x_4449_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
lean_dec(v___x_4452_);
lean_dec(v_rhs_4450_);
lean_dec(v_patType_x3f_4441_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_letOrReassign_4330_);
v___x_4455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4455_;
}
else
{
lean_object* v___x_4456_; lean_object* v_otherwise_x3f_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4456_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4457_ = l_Lean_Syntax_getArg(v___x_4452_, v___x_4439_);
v___x_4458_ = l_Lean_Syntax_getArg(v___x_4452_, v___x_4456_);
lean_dec(v___x_4452_);
v___x_4459_ = l_Lean_Syntax_getOptional_x3f(v___x_4458_);
lean_dec(v___x_4458_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_box(0);
v___y_4384_ = v___y_4448_;
v___y_4385_ = v_patType_x3f_4441_;
v___y_4386_ = v_rhs_4450_;
v___y_4387_ = v___y_4445_;
v___y_4388_ = v___y_4442_;
v___y_4389_ = v___y_4443_;
v___y_4390_ = v___y_4446_;
v___y_4391_ = v___y_4447_;
v___y_4392_ = v_otherwise_x3f_4457_;
v___y_4393_ = v___y_4444_;
v___y_4394_ = v___x_4460_;
goto v___jp_4383_;
}
else
{
lean_object* v_val_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
v_val_4461_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4459_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_val_4461_);
lean_dec(v___x_4459_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_val_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
v___y_4384_ = v___y_4448_;
v___y_4385_ = v_patType_x3f_4441_;
v___y_4386_ = v_rhs_4450_;
v___y_4387_ = v___y_4445_;
v___y_4388_ = v___y_4442_;
v___y_4389_ = v___y_4443_;
v___y_4390_ = v___y_4446_;
v___y_4391_ = v___y_4447_;
v___y_4392_ = v_otherwise_x3f_4457_;
v___y_4393_ = v___y_4444_;
v___y_4394_ = v___x_4466_;
goto v___jp_4383_;
}
}
}
}
}
else
{
lean_object* v___x_4469_; 
lean_dec(v___x_4452_);
v___x_4469_ = lean_box(0);
v___y_4355_ = v___y_4446_;
v___y_4356_ = v___x_4469_;
v___y_4357_ = v_patType_x3f_4441_;
v___y_4358_ = v___y_4448_;
v___y_4359_ = v_rhs_4450_;
v___y_4360_ = v___y_4443_;
v___y_4361_ = v___y_4447_;
v___y_4362_ = v___y_4445_;
v___y_4363_ = v___y_4442_;
v___y_4364_ = v___y_4444_;
v___y_4365_ = v___x_4469_;
goto v___jp_4354_;
}
}
}
else
{
lean_object* v_pattern_4481_; lean_object* v___x_4482_; lean_object* v_patType_x3f_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v_pattern_4481_ = l_Lean_Syntax_getArg(v___x_4351_, v___x_4350_);
v___x_4482_ = lean_unsigned_to_nat(1u);
v___x_4539_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4482_);
v___x_4540_ = l_Lean_Syntax_isNone(v___x_4539_);
if (v___x_4540_ == 0)
{
uint8_t v___x_4541_; 
lean_inc(v___x_4539_);
v___x_4541_ = l_Lean_Syntax_matchesNull(v___x_4539_, v___x_4482_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; 
lean_dec(v___x_4539_);
lean_dec(v_pattern_4481_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4543_ = l_Lean_Syntax_getArg(v___x_4539_, v___x_4350_);
lean_dec(v___x_4539_);
v___x_4544_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4543_);
v___x_4545_ = l_Lean_Syntax_isOfKind(v___x_4543_, v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
lean_dec(v___x_4543_);
lean_dec(v_pattern_4481_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4546_;
}
else
{
lean_object* v_patType_x3f_4547_; lean_object* v___x_4548_; 
v_patType_x3f_4547_ = l_Lean_Syntax_getArg(v___x_4543_, v___x_4482_);
lean_dec(v___x_4543_);
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_patType_x3f_4547_);
v_patType_x3f_4484_ = v___x_4548_;
v___y_4485_ = v_a_4334_;
v___y_4486_ = v_a_4335_;
v___y_4487_ = v_a_4336_;
v___y_4488_ = v_a_4337_;
v___y_4489_ = v_a_4338_;
v___y_4490_ = v_a_4339_;
v___y_4491_ = v_a_4340_;
goto v___jp_4483_;
}
}
}
else
{
lean_object* v___x_4549_; 
lean_dec(v___x_4539_);
v___x_4549_ = lean_box(0);
v_patType_x3f_4484_ = v___x_4549_;
v___y_4485_ = v_a_4334_;
v___y_4486_ = v_a_4335_;
v___y_4487_ = v_a_4336_;
v___y_4488_ = v_a_4337_;
v___y_4489_ = v_a_4338_;
v___y_4490_ = v_a_4339_;
v___y_4491_ = v_a_4340_;
goto v___jp_4483_;
}
v___jp_4483_:
{
lean_object* v___x_4492_; lean_object* v_rhs_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; uint8_t v___x_4496_; 
v___x_4492_ = lean_unsigned_to_nat(3u);
v_rhs_4493_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4492_);
v___x_4494_ = lean_unsigned_to_nat(4u);
v___x_4495_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4494_);
lean_dec(v_stx_4331_);
lean_inc(v___x_4495_);
v___x_4496_ = l_Lean_Syntax_matchesNull(v___x_4495_, v___x_4350_);
if (v___x_4496_ == 0)
{
uint8_t v___x_4497_; 
lean_dec(v_pattern_4481_);
v___x_4497_ = l_Lean_Syntax_isNone(v___x_4495_);
if (v___x_4497_ == 0)
{
uint8_t v___x_4498_; 
lean_inc(v___x_4495_);
v___x_4498_ = l_Lean_Syntax_matchesNull(v___x_4495_, v___x_4492_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
lean_dec(v___x_4495_);
lean_dec(v_rhs_4493_);
lean_dec(v_patType_x3f_4484_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_letOrReassign_4330_);
v___x_4499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; lean_object* v_otherwise_x3f_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4500_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4501_ = l_Lean_Syntax_getArg(v___x_4495_, v___x_4482_);
v___x_4502_ = l_Lean_Syntax_getArg(v___x_4495_, v___x_4500_);
lean_dec(v___x_4495_);
v___x_4503_ = l_Lean_Syntax_getOptional_x3f(v___x_4502_);
lean_dec(v___x_4502_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v___x_4504_; 
v___x_4504_ = lean_box(0);
v___y_4427_ = v___y_4487_;
v___y_4428_ = v_patType_x3f_4484_;
v___y_4429_ = v___y_4488_;
v___y_4430_ = v_otherwise_x3f_4501_;
v___y_4431_ = v___y_4490_;
v___y_4432_ = v___y_4485_;
v___y_4433_ = v___y_4489_;
v___y_4434_ = v___y_4491_;
v___y_4435_ = v_rhs_4493_;
v___y_4436_ = v___y_4486_;
v___y_4437_ = v___x_4504_;
goto v___jp_4426_;
}
else
{
lean_object* v_val_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
v_val_4505_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4503_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_val_4505_);
lean_dec(v___x_4503_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_val_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
v___y_4427_ = v___y_4487_;
v___y_4428_ = v_patType_x3f_4484_;
v___y_4429_ = v___y_4488_;
v___y_4430_ = v_otherwise_x3f_4501_;
v___y_4431_ = v___y_4490_;
v___y_4432_ = v___y_4485_;
v___y_4433_ = v___y_4489_;
v___y_4434_ = v___y_4491_;
v___y_4435_ = v_rhs_4493_;
v___y_4436_ = v___y_4486_;
v___y_4437_ = v___x_4510_;
goto v___jp_4426_;
}
}
}
}
}
else
{
lean_object* v___x_4513_; 
lean_dec(v___x_4495_);
v___x_4513_ = lean_box(0);
v___y_4397_ = v___x_4513_;
v___y_4398_ = v___y_4489_;
v___y_4399_ = v___y_4491_;
v___y_4400_ = v_rhs_4493_;
v___y_4401_ = v___y_4490_;
v___y_4402_ = v___y_4485_;
v___y_4403_ = v___y_4488_;
v___y_4404_ = v_patType_x3f_4484_;
v___y_4405_ = v___y_4486_;
v___y_4406_ = v___y_4487_;
v___y_4407_ = v___x_4513_;
goto v___jp_4396_;
}
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec(v___x_4495_);
lean_dec(v___x_4351_);
lean_dec(v_letOrReassign_4330_);
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4515_ = l_Lean_Core_mkFreshUserName(v___x_4514_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4517_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref_known(v___x_4515_, 1);
v___x_4517_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4333_, v_tk_4332_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; uint8_t v_kind_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v_kind_4519_ = lean_ctor_get_uint8(v_a_4518_, sizeof(void*)*3);
v___x_4520_ = l_Lean_mkIdentFrom(v_pattern_4481_, v_a_4516_, v___x_4346_);
lean_dec(v_pattern_4481_);
v___x_4521_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4521_, 0, v_a_4518_);
v___x_4522_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4520_, v_patType_x3f_4484_, v_rhs_4493_, v___x_4521_, v_kind_4519_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4522_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec(v_a_4516_);
lean_dec(v_rhs_4493_);
lean_dec(v_patType_x3f_4484_);
lean_dec(v_pattern_4481_);
v_a_4523_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4517_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4517_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec(v_rhs_4493_);
lean_dec(v_patType_x3f_4484_);
lean_dec(v_pattern_4481_);
lean_dec_ref(v_dec_4333_);
v_a_4531_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4515_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4515_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
v___jp_4354_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4367_ = l_Lean_Core_mkFreshUserName(v___x_4366_, v___y_4361_, v___y_4358_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___y_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
v___x_4369_ = l_Lean_mkIdentFrom(v___x_4351_, v_a_4368_, v___x_4353_);
v___x_4370_ = lean_box(v___x_4353_);
v___x_4371_ = lean_box(v___x_4348_);
lean_inc(v___x_4369_);
v___y_4372_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4372_, 0, v_letOrReassign_4330_);
lean_closure_set(v___y_4372_, 1, v___y_4356_);
lean_closure_set(v___y_4372_, 2, v___x_4370_);
lean_closure_set(v___y_4372_, 3, v___x_4342_);
lean_closure_set(v___y_4372_, 4, v___x_4343_);
lean_closure_set(v___y_4372_, 5, v___x_4344_);
lean_closure_set(v___y_4372_, 6, v___x_4351_);
lean_closure_set(v___y_4372_, 7, v___x_4369_);
lean_closure_set(v___y_4372_, 8, v_dec_4333_);
lean_closure_set(v___y_4372_, 9, v___x_4371_);
lean_closure_set(v___y_4372_, 10, v___y_4365_);
lean_closure_set(v___y_4372_, 11, v___x_4350_);
v___x_4373_ = 0;
v___x_4374_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4369_, v___y_4357_, v___y_4359_, v___y_4372_, v___x_4373_, v___y_4363_, v___y_4360_, v___y_4364_, v___y_4362_, v___y_4355_, v___y_4361_, v___y_4358_);
return v___x_4374_;
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v___y_4365_);
lean_dec(v___y_4359_);
lean_dec(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_letOrReassign_4330_);
v_a_4375_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4367_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4367_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
v___jp_4383_:
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___y_4392_);
v___y_4355_ = v___y_4390_;
v___y_4356_ = v___x_4395_;
v___y_4357_ = v___y_4385_;
v___y_4358_ = v___y_4384_;
v___y_4359_ = v___y_4386_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4391_;
v___y_4362_ = v___y_4387_;
v___y_4363_ = v___y_4388_;
v___y_4364_ = v___y_4393_;
v___y_4365_ = v___y_4394_;
goto v___jp_4354_;
}
v___jp_4396_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4409_ = l_Lean_Core_mkFreshUserName(v___x_4408_, v___y_4401_, v___y_4399_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___y_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l_Lean_mkIdentFrom(v___x_4351_, v_a_4410_, v___x_4346_);
v___x_4412_ = lean_box(v___x_4346_);
v___x_4413_ = lean_box(v___x_4348_);
v___x_4414_ = lean_box(v___x_4353_);
lean_inc(v___x_4411_);
v___y_4415_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4415_, 0, v_letOrReassign_4330_);
lean_closure_set(v___y_4415_, 1, v___y_4397_);
lean_closure_set(v___y_4415_, 2, v___x_4412_);
lean_closure_set(v___y_4415_, 3, v___x_4342_);
lean_closure_set(v___y_4415_, 4, v___x_4343_);
lean_closure_set(v___y_4415_, 5, v___x_4344_);
lean_closure_set(v___y_4415_, 6, v___x_4351_);
lean_closure_set(v___y_4415_, 7, v___x_4411_);
lean_closure_set(v___y_4415_, 8, v_dec_4333_);
lean_closure_set(v___y_4415_, 9, v___x_4413_);
lean_closure_set(v___y_4415_, 10, v___y_4407_);
lean_closure_set(v___y_4415_, 11, v___x_4350_);
lean_closure_set(v___y_4415_, 12, v___x_4414_);
v___x_4416_ = 0;
v___x_4417_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4411_, v___y_4404_, v___y_4400_, v___y_4415_, v___x_4416_, v___y_4402_, v___y_4405_, v___y_4406_, v___y_4403_, v___y_4398_, v___y_4401_, v___y_4399_);
return v___x_4417_;
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v___y_4407_);
lean_dec(v___y_4404_);
lean_dec(v___y_4400_);
lean_dec(v___y_4397_);
lean_dec(v___x_4351_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_letOrReassign_4330_);
v_a_4418_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4409_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4409_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
v___jp_4426_:
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___y_4430_);
v___y_4397_ = v___x_4438_;
v___y_4398_ = v___y_4433_;
v___y_4399_ = v___y_4434_;
v___y_4400_ = v___y_4435_;
v___y_4401_ = v___y_4431_;
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4429_;
v___y_4404_ = v___y_4428_;
v___y_4405_ = v___y_4436_;
v___y_4406_ = v___y_4427_;
v___y_4407_ = v___y_4437_;
goto v___jp_4396_;
}
}
}
else
{
lean_object* v___x_4550_; lean_object* v_x_4551_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v_xType_x3f_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v_xType_x3f_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4550_ = lean_unsigned_to_nat(0u);
v_x_4551_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4550_);
v___x_4624_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4551_);
v___x_4625_ = l_Lean_Syntax_isOfKind(v_x_4551_, v___x_4624_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v_x_4551_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4626_;
}
else
{
lean_object* v___x_4627_; lean_object* v___x_4628_; uint8_t v___x_4629_; 
v___x_4627_ = lean_unsigned_to_nat(1u);
v___x_4628_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4627_);
v___x_4629_ = l_Lean_Syntax_isNone(v___x_4628_);
if (v___x_4629_ == 0)
{
uint8_t v___x_4630_; 
lean_inc(v___x_4628_);
v___x_4630_ = l_Lean_Syntax_matchesNull(v___x_4628_, v___x_4627_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; 
lean_dec(v___x_4628_);
lean_dec(v_x_4551_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4631_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4632_ = l_Lean_Syntax_getArg(v___x_4628_, v___x_4550_);
lean_dec(v___x_4628_);
v___x_4633_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4632_);
v___x_4634_ = l_Lean_Syntax_isOfKind(v___x_4632_, v___x_4633_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; 
lean_dec(v___x_4632_);
lean_dec(v_x_4551_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v___x_4635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4635_;
}
else
{
lean_object* v_xType_x3f_4636_; lean_object* v___x_4637_; 
v_xType_x3f_4636_ = l_Lean_Syntax_getArg(v___x_4632_, v___x_4627_);
lean_dec(v___x_4632_);
v___x_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_xType_x3f_4636_);
v_xType_x3f_4569_ = v___x_4637_;
v___y_4570_ = v_a_4334_;
v___y_4571_ = v_a_4335_;
v___y_4572_ = v_a_4336_;
v___y_4573_ = v_a_4337_;
v___y_4574_ = v_a_4338_;
v___y_4575_ = v_a_4339_;
v___y_4576_ = v_a_4340_;
goto v___jp_4568_;
}
}
}
else
{
lean_object* v___x_4638_; 
lean_dec(v___x_4628_);
v___x_4638_ = lean_box(0);
v_xType_x3f_4569_ = v___x_4638_;
v___y_4570_ = v_a_4334_;
v___y_4571_ = v_a_4335_;
v___y_4572_ = v_a_4336_;
v___y_4573_ = v_a_4337_;
v___y_4574_ = v_a_4338_;
v___y_4575_ = v_a_4339_;
v___y_4576_ = v_a_4340_;
goto v___jp_4568_;
}
}
v___jp_4552_:
{
uint8_t v_kind_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v_kind_4563_ = lean_ctor_get_uint8(v___y_4553_, sizeof(void*)*3);
v___x_4564_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4330_);
lean_dec(v_letOrReassign_4330_);
v___x_4565_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4565_, 0, v___y_4553_);
lean_inc(v_x_4551_);
v___x_4566_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4566_, 0, lean_box(0));
lean_closure_set(v___x_4566_, 1, v___x_4564_);
lean_closure_set(v___x_4566_, 2, v_x_4551_);
lean_closure_set(v___x_4566_, 3, v___x_4565_);
v___x_4567_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4551_, v_xType_x3f_4555_, v___y_4554_, v___x_4566_, v_kind_4563_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
return v___x_4567_;
}
v___jp_4568_:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4577_ = lean_unsigned_to_nat(1u);
v___x_4578_ = lean_mk_empty_array_with_capacity(v___x_4577_);
lean_inc(v_x_4551_);
v___x_4579_ = lean_array_push(v___x_4578_, v_x_4551_);
v___x_4580_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4330_, v___x_4579_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
lean_dec_ref(v___x_4579_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v___x_4581_; 
lean_dec_ref_known(v___x_4580_, 1);
v___x_4581_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4333_, v_tk_4332_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4583_; lean_object* v_rhs_4584_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
v___x_4583_ = lean_unsigned_to_nat(3u);
v_rhs_4584_ = l_Lean_Syntax_getArg(v_stx_4331_, v___x_4583_);
lean_dec(v_stx_4331_);
if (lean_obj_tag(v_letOrReassign_4330_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4569_) == 0)
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = l_Lean_TSyntax_getId(v_x_4551_);
v___x_4586_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4585_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4586_, 1);
v___x_4588_ = l_Lean_LocalDecl_type(v_a_4587_);
lean_dec(v_a_4587_);
v___x_4589_ = l_Lean_Elab_Term_exprToSyntax(v___x_4588_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4591_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref_known(v___x_4589_, 1);
v___x_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4591_, 0, v_a_4590_);
v___y_4553_ = v_a_4582_;
v___y_4554_ = v_rhs_4584_;
v_xType_x3f_4555_ = v___x_4591_;
v___y_4556_ = v___y_4570_;
v___y_4557_ = v___y_4571_;
v___y_4558_ = v___y_4572_;
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___y_4574_;
v___y_4561_ = v___y_4575_;
v___y_4562_ = v___y_4576_;
goto v___jp_4552_;
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec(v_rhs_4584_);
lean_dec(v_a_4582_);
lean_dec(v_x_4551_);
v_a_4592_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4589_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4589_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec(v_rhs_4584_);
lean_dec(v_a_4582_);
lean_dec(v_x_4551_);
v_a_4600_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4586_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4586_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
else
{
v___y_4553_ = v_a_4582_;
v___y_4554_ = v_rhs_4584_;
v_xType_x3f_4555_ = v_xType_x3f_4569_;
v___y_4556_ = v___y_4570_;
v___y_4557_ = v___y_4571_;
v___y_4558_ = v___y_4572_;
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___y_4574_;
v___y_4561_ = v___y_4575_;
v___y_4562_ = v___y_4576_;
goto v___jp_4552_;
}
}
else
{
v___y_4553_ = v_a_4582_;
v___y_4554_ = v_rhs_4584_;
v_xType_x3f_4555_ = v_xType_x3f_4569_;
v___y_4556_ = v___y_4570_;
v___y_4557_ = v___y_4571_;
v___y_4558_ = v___y_4572_;
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___y_4574_;
v___y_4561_ = v___y_4575_;
v___y_4562_ = v___y_4576_;
goto v___jp_4552_;
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v_xType_x3f_4569_);
lean_dec(v_x_4551_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v_a_4608_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4581_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4581_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
lean_dec(v_xType_x3f_4569_);
lean_dec(v_x_4551_);
lean_dec_ref(v_dec_4333_);
lean_dec(v_stx_4331_);
lean_dec(v_letOrReassign_4330_);
v_a_4616_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4580_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4580_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4639_, lean_object* v_stx_4640_, lean_object* v_tk_4641_, lean_object* v_dec_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4639_, v_stx_4640_, v_tk_4641_, v_dec_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_tk_4641_);
return v_res_4651_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4654_ = l_Lean_stringToMessageData(v___x_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4655_, lean_object* v_mutTk_x3f_4656_, lean_object* v_initConfig_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4656_) == 0)
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4655_, v_initConfig_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
return v___x_4665_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = l_Lean_Syntax_getArg(v_letConfigStx_4655_, v___x_4666_);
v___x_4668_ = l_Lean_Syntax_getArgs(v___x_4667_);
lean_dec(v___x_4667_);
v___x_4669_ = lean_array_get_size(v___x_4668_);
lean_dec_ref(v___x_4668_);
v___x_4670_ = lean_nat_dec_eq(v___x_4669_, v___x_4666_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v_initConfig_4657_);
v___x_4671_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4672_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4655_, v___x_4671_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec(v_letConfigStx_4655_);
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
else
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4655_, v_initConfig_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
return v___x_4681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4682_, lean_object* v_mutTk_x3f_4683_, lean_object* v_initConfig_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4682_, v_mutTk_x3f_4683_, v_initConfig_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_mutTk_x3f_4683_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4693_, lean_object* v_mutTk_x3f_4694_, lean_object* v_initConfig_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4693_, v_mutTk_x3f_4694_, v_initConfig_4695_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4705_, lean_object* v_mutTk_x3f_4706_, lean_object* v_initConfig_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4705_, v_mutTk_x3f_4706_, v_initConfig_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_mutTk_x3f_4706_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4730_, lean_object* v_dec_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4740_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4730_);
v___x_4741_ = l_Lean_Syntax_isOfKind(v_stx_4730_, v___x_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; 
lean_dec_ref(v_dec_4731_);
lean_dec(v_stx_4730_);
v___x_4742_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4742_;
}
else
{
lean_object* v___x_4743_; lean_object* v_tk_4744_; lean_object* v_mutTk_x3f_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___x_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v___x_4743_ = lean_unsigned_to_nat(0u);
v_tk_4744_ = l_Lean_Syntax_getArg(v_stx_4730_, v___x_4743_);
v___x_4777_ = lean_unsigned_to_nat(1u);
v___x_4778_ = l_Lean_Syntax_getArg(v_stx_4730_, v___x_4777_);
v___x_4779_ = l_Lean_Syntax_isNone(v___x_4778_);
if (v___x_4779_ == 0)
{
uint8_t v___x_4780_; 
lean_inc(v___x_4778_);
v___x_4780_ = l_Lean_Syntax_matchesNull(v___x_4778_, v___x_4777_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; 
lean_dec(v___x_4778_);
lean_dec(v_tk_4744_);
lean_dec_ref(v_dec_4731_);
lean_dec(v_stx_4730_);
v___x_4781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4781_;
}
else
{
lean_object* v_mutTk_x3f_4782_; lean_object* v___x_4783_; 
v_mutTk_x3f_4782_ = l_Lean_Syntax_getArg(v___x_4778_, v___x_4743_);
lean_dec(v___x_4778_);
v___x_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_mutTk_x3f_4782_);
v_mutTk_x3f_4746_ = v___x_4783_;
v___y_4747_ = v_a_4732_;
v___y_4748_ = v_a_4733_;
v___y_4749_ = v_a_4734_;
v___y_4750_ = v_a_4735_;
v___y_4751_ = v_a_4736_;
v___y_4752_ = v_a_4737_;
v___y_4753_ = v_a_4738_;
goto v___jp_4745_;
}
}
else
{
lean_object* v___x_4784_; 
lean_dec(v___x_4778_);
v___x_4784_ = lean_box(0);
v_mutTk_x3f_4746_ = v___x_4784_;
v___y_4747_ = v_a_4732_;
v___y_4748_ = v_a_4733_;
v___y_4749_ = v_a_4734_;
v___y_4750_ = v_a_4735_;
v___y_4751_ = v_a_4736_;
v___y_4752_ = v_a_4737_;
v___y_4753_ = v_a_4738_;
goto v___jp_4745_;
}
v___jp_4745_:
{
lean_object* v___x_4754_; lean_object* v_config_4755_; lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4754_ = lean_unsigned_to_nat(2u);
v_config_4755_ = l_Lean_Syntax_getArg(v_stx_4730_, v___x_4754_);
v___x_4756_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4755_);
v___x_4757_ = l_Lean_Syntax_isOfKind(v_config_4755_, v___x_4756_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; 
lean_dec(v_config_4755_);
lean_dec(v_mutTk_x3f_4746_);
lean_dec(v_tk_4744_);
lean_dec_ref(v_dec_4731_);
lean_dec(v_stx_4730_);
v___x_4758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4758_;
}
else
{
lean_object* v___x_4759_; lean_object* v_decl_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4759_ = lean_unsigned_to_nat(3u);
v_decl_4760_ = l_Lean_Syntax_getArg(v_stx_4730_, v___x_4759_);
lean_dec(v_stx_4730_);
v___x_4761_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4760_);
v___x_4762_ = l_Lean_Syntax_isOfKind(v_decl_4760_, v___x_4761_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; 
lean_dec(v_decl_4760_);
lean_dec(v_config_4755_);
lean_dec(v_mutTk_x3f_4746_);
lean_dec(v_tk_4744_);
lean_dec_ref(v_dec_4731_);
v___x_4763_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4763_;
}
else
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4765_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4755_, v_mutTk_x3f_4746_, v___x_4764_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v_mutTk_x3f_4746_);
v___x_4768_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4766_, v___x_4767_, v_decl_4760_, v_tk_4744_, v_dec_4731_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_);
return v___x_4768_;
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
lean_dec(v_decl_4760_);
lean_dec(v_mutTk_x3f_4746_);
lean_dec(v_tk_4744_);
lean_dec_ref(v_dec_4731_);
v_a_4769_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4765_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4765_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4785_, lean_object* v_dec_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l_Lean_Elab_Do_elabDoLet(v_stx_4785_, v_dec_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec_ref(v_a_4787_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4803_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4804_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4805_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4806_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4807_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4803_, v___x_4804_, v___x_4805_, v___x_4806_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4815_, lean_object* v_dec_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v___x_4825_; uint8_t v___x_4826_; 
v___x_4825_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4815_);
v___x_4826_ = l_Lean_Syntax_isOfKind(v_stx_4815_, v___x_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; 
lean_dec_ref(v_dec_4816_);
lean_dec(v_stx_4815_);
v___x_4827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = l_Lean_Syntax_getArg(v_stx_4815_, v___x_4828_);
v___x_4830_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4829_);
v___x_4831_ = l_Lean_Syntax_isOfKind(v___x_4829_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_object* v___x_4832_; 
lean_dec(v___x_4829_);
lean_dec_ref(v_dec_4816_);
lean_dec(v_stx_4815_);
v___x_4832_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4832_;
}
else
{
lean_object* v___x_4833_; lean_object* v_decl_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4833_ = lean_unsigned_to_nat(2u);
v_decl_4834_ = l_Lean_Syntax_getArg(v_stx_4815_, v___x_4833_);
v___x_4835_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4834_);
v___x_4836_ = l_Lean_Syntax_isOfKind(v_decl_4834_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; 
lean_dec(v_decl_4834_);
lean_dec(v___x_4829_);
lean_dec_ref(v_dec_4816_);
lean_dec(v_stx_4815_);
v___x_4837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4837_;
}
else
{
uint8_t v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4838_ = 0;
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set_uint8(v___x_4840_, sizeof(void*)*1, v___x_4836_);
lean_ctor_set_uint8(v___x_4840_, sizeof(void*)*1 + 1, v___x_4838_);
lean_ctor_set_uint8(v___x_4840_, sizeof(void*)*1 + 2, v___x_4838_);
lean_ctor_set_uint8(v___x_4840_, sizeof(void*)*1 + 3, v___x_4838_);
lean_ctor_set_uint8(v___x_4840_, sizeof(void*)*1 + 4, v___x_4838_);
v___x_4841_ = l_Lean_Elab_Term_mkLetConfig(v___x_4829_, v___x_4840_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4843_; lean_object* v_tk_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4841_, 1);
v___x_4843_ = lean_unsigned_to_nat(0u);
v_tk_4844_ = l_Lean_Syntax_getArg(v_stx_4815_, v___x_4843_);
lean_dec(v_stx_4815_);
v___x_4845_ = lean_box(1);
v___x_4846_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4842_, v___x_4845_, v_decl_4834_, v_tk_4844_, v_dec_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
return v___x_4846_;
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec(v_decl_4834_);
lean_dec_ref(v_dec_4816_);
lean_dec(v_stx_4815_);
v_a_4847_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4841_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4841_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4855_, lean_object* v_dec_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_Elab_Do_elabDoHave(v_stx_4855_, v_dec_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
lean_dec(v_a_4863_);
lean_dec_ref(v_a_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec_ref(v_a_4857_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4873_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4874_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4876_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4877_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4873_, v___x_4874_, v___x_4875_, v___x_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v___x_4884_, lean_object* v___x_4885_, lean_object* v_decls_4886_, lean_object* v_a_4887_, uint8_t v___x_4888_, lean_object* v_body_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_ref_4898_; uint8_t v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v_ref_4898_ = lean_ctor_get(v___y_4895_, 5);
v___x_4899_ = 0;
v___x_4900_ = l_Lean_SourceInfo_fromRef(v_ref_4898_, v___x_4899_);
v___x_4901_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4902_ = l_Lean_Name_mkStr4(v___x_4882_, v___x_4883_, v___x_4884_, v___x_4901_);
v___x_4903_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4900_, 4);
v___x_4904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4900_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4900_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = l_Lean_Syntax_node2(v___x_4900_, v___x_4885_, v___x_4904_, v___x_4906_);
v___x_4908_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4900_);
lean_ctor_set(v___x_4909_, 1, v___x_4908_);
v___x_4910_ = l_Lean_Syntax_node4(v___x_4900_, v___x_4902_, v___x_4907_, v_decls_4886_, v___x_4909_, v_body_4889_);
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_a_4887_);
v___x_4912_ = l_Lean_Elab_Term_elabTerm(v___x_4910_, v___x_4911_, v___x_4888_, v___x_4888_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4913_, lean_object* v___x_4914_, lean_object* v___x_4915_, lean_object* v___x_4916_, lean_object* v_decls_4917_, lean_object* v_a_4918_, lean_object* v___x_4919_, lean_object* v_body_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
uint8_t v___x_5027__boxed_4929_; lean_object* v_res_4930_; 
v___x_5027__boxed_4929_ = lean_unbox(v___x_4919_);
v_res_4930_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4913_, v___x_4914_, v___x_4915_, v___x_4916_, v_decls_4917_, v_a_4918_, v___x_5027__boxed_4929_, v_body_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec_ref(v___y_4921_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
if (lean_obj_tag(v_a_4931_) == 0)
{
lean_object* v___x_4933_; 
v___x_4933_ = l_List_reverse___redArg(v_a_4932_);
return v___x_4933_;
}
else
{
lean_object* v_head_4934_; lean_object* v_tail_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4944_; 
v_head_4934_ = lean_ctor_get(v_a_4931_, 0);
v_tail_4935_ = lean_ctor_get(v_a_4931_, 1);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_a_4931_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4937_ = v_a_4931_;
v_isShared_4938_ = v_isSharedCheck_4944_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_tail_4935_);
lean_inc(v_head_4934_);
lean_dec(v_a_4931_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4944_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4939_ = l_Lean_MessageData_ofSyntax(v_head_4934_);
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 1, v_a_4932_);
lean_ctor_set(v___x_4937_, 0, v___x_4939_);
v___x_4941_ = v___x_4937_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4939_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_a_4932_);
v___x_4941_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
v_a_4931_ = v_tail_4935_;
v_a_4932_ = v___x_4941_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4962_ = l_Lean_stringToMessageData(v___x_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4963_, lean_object* v_dec_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
v___x_4973_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4974_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4975_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4976_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4963_);
v___x_4977_ = l_Lean_Syntax_isOfKind(v_stx_4963_, v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; 
lean_dec_ref(v_dec_4964_);
lean_dec(v_stx_4963_);
v___x_4978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4978_;
}
else
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = l_Lean_Syntax_getArg(v_stx_4963_, v___x_4979_);
v___x_4981_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4980_);
v___x_4982_ = l_Lean_Syntax_isOfKind(v___x_4980_, v___x_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
lean_dec(v___x_4980_);
lean_dec_ref(v_dec_4964_);
lean_dec(v_stx_4963_);
v___x_4983_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4983_;
}
else
{
lean_object* v___x_4984_; lean_object* v_decls_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; 
v___x_4984_ = lean_unsigned_to_nat(1u);
v_decls_4985_ = l_Lean_Syntax_getArg(v_stx_4963_, v___x_4984_);
lean_dec(v_stx_4963_);
v___x_4986_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4985_);
v___x_4987_ = l_Lean_Syntax_isOfKind(v_decls_4985_, v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
lean_dec(v_decls_4985_);
lean_dec(v___x_4980_);
lean_dec_ref(v_dec_4964_);
v___x_4988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4988_;
}
else
{
lean_object* v_tk_4989_; lean_object* v___x_4990_; 
v_tk_4989_ = l_Lean_Syntax_getArg(v___x_4980_, v___x_4979_);
lean_dec(v___x_4980_);
v___x_4990_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4964_, v_tk_4989_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
lean_dec(v_tk_4989_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4992_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
lean_inc(v_decls_4985_);
v___x_4992_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4985_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v_doBlockResultType_4994_; lean_object* v___x_4995_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref_known(v___x_4992_, 1);
v_doBlockResultType_4994_ = lean_ctor_get(v_a_4965_, 3);
lean_inc_ref(v_doBlockResultType_4994_);
v___x_4995_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4994_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4997_; lean_object* v___f_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v___x_4997_ = lean_box(v___x_4987_);
v___f_4998_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4998_, 0, v___x_4973_);
lean_closure_set(v___f_4998_, 1, v___x_4974_);
lean_closure_set(v___f_4998_, 2, v___x_4975_);
lean_closure_set(v___f_4998_, 3, v___x_4981_);
lean_closure_set(v___f_4998_, 4, v_decls_4985_);
lean_closure_set(v___f_4998_, 5, v_a_4996_);
lean_closure_set(v___f_4998_, 6, v___x_4997_);
v___x_4999_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5000_ = lean_array_to_list(v_a_4993_);
v___x_5001_ = lean_box(0);
v___x_5002_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5000_, v___x_5001_);
v___x_5003_ = l_Lean_MessageData_ofList(v___x_5002_);
v___x_5004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_4999_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
v___x_5005_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5005_, 0, v_a_4991_);
v___x_5006_ = lean_box(0);
v___x_5007_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5004_, v___x_5005_, v___f_4998_, v___x_5006_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_5007_;
}
else
{
lean_dec(v_a_4993_);
lean_dec(v_a_4991_);
lean_dec(v_decls_4985_);
return v___x_4995_;
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec(v_a_4991_);
lean_dec(v_decls_4985_);
v_a_5008_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4992_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4992_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec(v_decls_4985_);
v_a_5016_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_4990_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4990_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5024_, lean_object* v_dec_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5024_, v_dec_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec_ref(v_a_5026_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5042_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5043_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5044_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5045_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5046_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5042_, v___x_5043_, v___x_5044_, v___x_5045_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5062_, lean_object* v_dec_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; uint8_t v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5105_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_5062_);
v___x_5106_ = l_Lean_Syntax_isOfKind(v_stx_5062_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; 
lean_dec_ref(v_dec_5063_);
lean_dec(v_stx_5062_);
v___x_5107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5107_;
}
else
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = l_Lean_Syntax_getArg(v_stx_5062_, v___x_5108_);
lean_dec(v_stx_5062_);
v___x_5110_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5109_);
v___x_5111_ = l_Lean_Syntax_isOfKind(v___x_5109_, v___x_5110_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; uint8_t v___x_5113_; 
v___x_5112_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5109_);
v___x_5113_ = l_Lean_Syntax_isOfKind(v___x_5109_, v___x_5112_);
if (v___x_5113_ == 0)
{
lean_object* v___x_5114_; 
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v_decl_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5115_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5116_ = lean_unsigned_to_nat(1u);
v___x_5117_ = lean_mk_empty_array_with_capacity(v___x_5116_);
v___x_5118_ = lean_array_push(v___x_5117_, v___x_5109_);
v___x_5119_ = lean_box(2);
v_decl_5120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5120_, 0, v___x_5119_);
lean_ctor_set(v_decl_5120_, 1, v___x_5115_);
lean_ctor_set(v_decl_5120_, 2, v___x_5118_);
v___x_5121_ = lean_box(0);
v___x_5122_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1, v___x_5111_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1 + 1, v___x_5111_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1 + 2, v___x_5111_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1 + 3, v___x_5111_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1 + 4, v___x_5111_);
v___x_5123_ = lean_box(2);
lean_inc_ref(v_decl_5120_);
v___x_5124_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5122_, v___x_5123_, v_decl_5120_, v_decl_5120_, v_dec_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
return v___x_5124_;
}
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5126_; uint8_t v___x_5127_; 
v___x_5125_ = l_Lean_Syntax_getArg(v___x_5109_, v___x_5108_);
v___x_5126_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5125_);
v___x_5127_ = l_Lean_Syntax_isOfKind(v___x_5125_, v___x_5126_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
lean_dec(v___x_5125_);
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5128_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5128_;
}
else
{
lean_object* v___x_5129_; lean_object* v_xType_x3f_5131_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5129_ = l_Lean_Syntax_getArg(v___x_5125_, v___x_5108_);
lean_dec(v___x_5125_);
v___x_5158_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5129_);
v___x_5159_ = l_Lean_Syntax_isOfKind(v___x_5129_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_object* v___x_5160_; 
lean_dec(v___x_5129_);
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5160_;
}
else
{
lean_object* v___x_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; 
v___x_5161_ = lean_unsigned_to_nat(1u);
v___x_5162_ = l_Lean_Syntax_getArg(v___x_5109_, v___x_5161_);
v___x_5163_ = l_Lean_Syntax_matchesNull(v___x_5162_, v___x_5108_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; 
lean_dec(v___x_5129_);
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5164_;
}
else
{
lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = lean_unsigned_to_nat(2u);
v___x_5166_ = l_Lean_Syntax_getArg(v___x_5109_, v___x_5165_);
v___x_5167_ = l_Lean_Syntax_isNone(v___x_5166_);
if (v___x_5167_ == 0)
{
uint8_t v___x_5168_; 
lean_inc(v___x_5166_);
v___x_5168_ = l_Lean_Syntax_matchesNull(v___x_5166_, v___x_5161_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; 
lean_dec(v___x_5166_);
lean_dec(v___x_5129_);
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5169_;
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v___x_5170_ = l_Lean_Syntax_getArg(v___x_5166_, v___x_5108_);
lean_dec(v___x_5166_);
v___x_5171_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5170_);
v___x_5172_ = l_Lean_Syntax_isOfKind(v___x_5170_, v___x_5171_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; 
lean_dec(v___x_5170_);
lean_dec(v___x_5129_);
lean_dec(v___x_5109_);
lean_dec_ref(v_dec_5063_);
v___x_5173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5173_;
}
else
{
lean_object* v_xType_x3f_5174_; lean_object* v___x_5175_; 
v_xType_x3f_5174_ = l_Lean_Syntax_getArg(v___x_5170_, v___x_5161_);
lean_dec(v___x_5170_);
v___x_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5175_, 0, v_xType_x3f_5174_);
v_xType_x3f_5131_ = v___x_5175_;
v___y_5132_ = v_a_5064_;
v___y_5133_ = v_a_5065_;
v___y_5134_ = v_a_5066_;
v___y_5135_ = v_a_5067_;
v___y_5136_ = v_a_5068_;
v___y_5137_ = v_a_5069_;
v___y_5138_ = v_a_5070_;
goto v___jp_5130_;
}
}
}
else
{
lean_object* v___x_5176_; 
lean_dec(v___x_5166_);
v___x_5176_ = lean_box(0);
v_xType_x3f_5131_ = v___x_5176_;
v___y_5132_ = v_a_5064_;
v___y_5133_ = v_a_5065_;
v___y_5134_ = v_a_5066_;
v___y_5135_ = v_a_5067_;
v___y_5136_ = v_a_5068_;
v___y_5137_ = v_a_5069_;
v___y_5138_ = v_a_5070_;
goto v___jp_5130_;
}
}
}
v___jp_5130_:
{
lean_object* v_ref_5139_; lean_object* v___x_5140_; lean_object* v_tk_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; uint8_t v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
v_ref_5139_ = lean_ctor_get(v___y_5137_, 5);
v___x_5140_ = lean_unsigned_to_nat(3u);
v_tk_5141_ = l_Lean_Syntax_getArg(v___x_5109_, v___x_5140_);
v___x_5142_ = lean_unsigned_to_nat(4u);
v___x_5143_ = l_Lean_Syntax_getArg(v___x_5109_, v___x_5142_);
lean_dec(v___x_5109_);
v___x_5144_ = 0;
v___x_5145_ = l_Lean_SourceInfo_fromRef(v_ref_5139_, v___x_5144_);
v___x_5146_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5145_, 2);
v___x_5147_ = l_Lean_Syntax_node1(v___x_5145_, v___x_5126_, v___x_5129_);
v___x_5148_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5149_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5145_);
lean_ctor_set(v___x_5150_, 1, v___x_5148_);
lean_ctor_set(v___x_5150_, 2, v___x_5149_);
if (lean_obj_tag(v_xType_x3f_5131_) == 1)
{
lean_object* v_val_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v_val_5151_ = lean_ctor_get(v_xType_x3f_5131_, 0);
lean_inc(v_val_5151_);
lean_dec_ref_known(v_xType_x3f_5131_, 1);
v___x_5152_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5153_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5145_, 2);
v___x_5154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5145_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
v___x_5155_ = l_Lean_Syntax_node2(v___x_5145_, v___x_5152_, v___x_5154_, v_val_5151_);
v___x_5156_ = l_Array_mkArray1___redArg(v___x_5155_);
v___y_5073_ = v___x_5149_;
v___y_5074_ = v___y_5133_;
v___y_5075_ = v___y_5138_;
v___y_5076_ = v___x_5148_;
v___y_5077_ = v___x_5145_;
v___y_5078_ = v___y_5137_;
v___y_5079_ = v___x_5147_;
v___y_5080_ = v___x_5143_;
v___y_5081_ = v___x_5150_;
v___y_5082_ = v_tk_5141_;
v___y_5083_ = v___y_5134_;
v___y_5084_ = v___y_5135_;
v___y_5085_ = v___x_5144_;
v___y_5086_ = v___y_5136_;
v___y_5087_ = v___y_5132_;
v___y_5088_ = v___x_5146_;
v___y_5089_ = v___x_5156_;
goto v___jp_5072_;
}
else
{
lean_object* v___x_5157_; 
lean_dec(v_xType_x3f_5131_);
v___x_5157_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_5073_ = v___x_5149_;
v___y_5074_ = v___y_5133_;
v___y_5075_ = v___y_5138_;
v___y_5076_ = v___x_5148_;
v___y_5077_ = v___x_5145_;
v___y_5078_ = v___y_5137_;
v___y_5079_ = v___x_5147_;
v___y_5080_ = v___x_5143_;
v___y_5081_ = v___x_5150_;
v___y_5082_ = v_tk_5141_;
v___y_5083_ = v___y_5134_;
v___y_5084_ = v___y_5135_;
v___y_5085_ = v___x_5144_;
v___y_5086_ = v___y_5136_;
v___y_5087_ = v___y_5132_;
v___y_5088_ = v___x_5146_;
v___y_5089_ = v___x_5157_;
goto v___jp_5072_;
}
}
}
}
}
v___jp_5072_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_inc_ref(v___y_5073_);
v___x_5090_ = l_Array_append___redArg(v___y_5073_, v___y_5089_);
lean_dec_ref(v___y_5089_);
lean_inc(v___y_5076_);
lean_inc_n(v___y_5077_, 2);
v___x_5091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5091_, 0, v___y_5077_);
lean_ctor_set(v___x_5091_, 1, v___y_5076_);
lean_ctor_set(v___x_5091_, 2, v___x_5090_);
v___x_5092_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5093_, 0, v___y_5077_);
lean_ctor_set(v___x_5093_, 1, v___x_5092_);
lean_inc(v___y_5088_);
v___x_5094_ = l_Lean_Syntax_node5(v___y_5077_, v___y_5088_, v___y_5079_, v___y_5081_, v___x_5091_, v___x_5093_, v___y_5080_);
v___x_5095_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5096_ = lean_unsigned_to_nat(1u);
v___x_5097_ = lean_mk_empty_array_with_capacity(v___x_5096_);
v___x_5098_ = lean_array_push(v___x_5097_, v___x_5094_);
v___x_5099_ = lean_box(2);
v___x_5100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
lean_ctor_set(v___x_5100_, 1, v___x_5095_);
lean_ctor_set(v___x_5100_, 2, v___x_5098_);
v___x_5101_ = lean_box(0);
v___x_5102_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1, v___y_5085_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1 + 1, v___y_5085_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1 + 2, v___y_5085_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1 + 3, v___y_5085_);
lean_ctor_set_uint8(v___x_5102_, sizeof(void*)*1 + 4, v___y_5085_);
v___x_5103_ = lean_box(2);
v___x_5104_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5102_, v___x_5103_, v___x_5100_, v___y_5082_, v_dec_5063_, v___y_5087_, v___y_5074_, v___y_5083_, v___y_5084_, v___y_5086_, v___y_5078_, v___y_5075_);
return v___x_5104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5177_, lean_object* v_dec_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5177_, v_dec_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
lean_dec(v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec(v_a_5183_);
lean_dec_ref(v_a_5182_);
lean_dec(v_a_5181_);
lean_dec_ref(v_a_5180_);
lean_dec_ref(v_a_5179_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5195_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5196_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5197_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5198_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5199_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5195_, v___x_5196_, v___x_5197_, v___x_5198_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
uint8_t v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5211_ = 0;
v___x_5212_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5202_, v___x_5211_);
v___x_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v_____do__lift_5214_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5243_, size_t v_sz_5244_, size_t v_i_5245_, lean_object* v_b_5246_, lean_object* v___y_5247_){
_start:
{
uint8_t v___x_5249_; 
v___x_5249_ = lean_usize_dec_lt(v_i_5245_, v_sz_5244_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; 
v___x_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5250_, 0, v_b_5246_);
return v___x_5250_;
}
else
{
lean_object* v_ref_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v_a_5254_; uint8_t v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; size_t v___x_5288_; size_t v___x_5289_; 
v_ref_5251_ = lean_ctor_get(v___y_5247_, 5);
v___x_5252_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5254_ = lean_array_uget_borrowed(v_as_5243_, v_i_5245_);
v___x_5255_ = 0;
v___x_5256_ = l_Lean_SourceInfo_fromRef(v_ref_5251_, v___x_5255_);
v___x_5257_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5259_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5260_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5256_, 17);
v___x_5261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5256_);
lean_ctor_set(v___x_5261_, 1, v___x_5260_);
v___x_5262_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5256_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
v___x_5264_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5257_, v___x_5263_);
v___x_5265_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5256_);
lean_ctor_set(v___x_5266_, 1, v___x_5257_);
lean_ctor_set(v___x_5266_, 2, v___x_5265_);
lean_inc_ref_n(v___x_5266_, 3);
v___x_5267_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5252_, v___x_5266_);
v___x_5268_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5269_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5270_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5254_, 2);
v___x_5271_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5270_, v_a_5254_);
v___x_5272_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5256_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
v___x_5274_ = l_Lean_Syntax_node5(v___x_5256_, v___x_5269_, v___x_5271_, v___x_5266_, v___x_5266_, v___x_5273_, v_a_5254_);
v___x_5275_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5268_, v___x_5274_);
v___x_5276_ = l_Lean_Syntax_node4(v___x_5256_, v___x_5259_, v___x_5261_, v___x_5264_, v___x_5267_, v___x_5275_);
v___x_5277_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5256_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5257_, v___x_5278_);
v___x_5280_ = l_Lean_Syntax_node2(v___x_5256_, v___x_5258_, v___x_5276_, v___x_5279_);
v___x_5281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5256_);
lean_ctor_set(v___x_5283_, 1, v___x_5282_);
v___x_5284_ = l_Lean_Syntax_node2(v___x_5256_, v___x_5281_, v___x_5283_, v_b_5246_);
v___x_5285_ = l_Lean_Syntax_node2(v___x_5256_, v___x_5258_, v___x_5284_, v___x_5266_);
v___x_5286_ = l_Lean_Syntax_node2(v___x_5256_, v___x_5257_, v___x_5280_, v___x_5285_);
v___x_5287_ = l_Lean_Syntax_node1(v___x_5256_, v___x_5253_, v___x_5286_);
v___x_5288_ = ((size_t)1ULL);
v___x_5289_ = lean_usize_add(v_i_5245_, v___x_5288_);
v_i_5245_ = v___x_5289_;
v_b_5246_ = v___x_5287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5291_, lean_object* v_sz_5292_, lean_object* v_i_5293_, lean_object* v_b_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
size_t v_sz_boxed_5297_; size_t v_i_boxed_5298_; lean_object* v_res_5299_; 
v_sz_boxed_5297_ = lean_unbox_usize(v_sz_5292_);
lean_dec(v_sz_5292_);
v_i_boxed_5298_ = lean_unbox_usize(v_i_5293_);
lean_dec(v_i_5293_);
v_res_5299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5291_, v_sz_boxed_5297_, v_i_boxed_5298_, v_b_5294_, v___y_5295_);
lean_dec_ref(v___y_5295_);
lean_dec_ref(v_as_5291_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5300_, size_t v_sz_5301_, size_t v_i_5302_, lean_object* v_b_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
uint8_t v___x_5312_; 
v___x_5312_ = lean_usize_dec_lt(v_i_5302_, v_sz_5301_);
if (v___x_5312_ == 0)
{
lean_object* v___x_5313_; 
v___x_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5313_, 0, v_b_5303_);
return v___x_5313_;
}
else
{
lean_object* v_ref_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v_a_5317_; uint8_t v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v_ref_5314_ = lean_ctor_get(v___y_5309_, 5);
v___x_5315_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5317_ = lean_array_uget_borrowed(v_as_5300_, v_i_5302_);
v___x_5318_ = 0;
v___x_5319_ = l_Lean_SourceInfo_fromRef(v_ref_5314_, v___x_5318_);
v___x_5320_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5323_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5319_, 17);
v___x_5324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5319_);
lean_ctor_set(v___x_5324_, 1, v___x_5323_);
v___x_5325_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5326_, 0, v___x_5319_);
lean_ctor_set(v___x_5326_, 1, v___x_5325_);
v___x_5327_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5320_, v___x_5326_);
v___x_5328_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5319_);
lean_ctor_set(v___x_5329_, 1, v___x_5320_);
lean_ctor_set(v___x_5329_, 2, v___x_5328_);
lean_inc_ref_n(v___x_5329_, 3);
v___x_5330_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5315_, v___x_5329_);
v___x_5331_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5332_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5333_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5317_, 2);
v___x_5334_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5333_, v_a_5317_);
v___x_5335_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5319_);
lean_ctor_set(v___x_5336_, 1, v___x_5335_);
v___x_5337_ = l_Lean_Syntax_node5(v___x_5319_, v___x_5332_, v___x_5334_, v___x_5329_, v___x_5329_, v___x_5336_, v_a_5317_);
v___x_5338_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5331_, v___x_5337_);
v___x_5339_ = l_Lean_Syntax_node4(v___x_5319_, v___x_5322_, v___x_5324_, v___x_5327_, v___x_5330_, v___x_5338_);
v___x_5340_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5319_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5320_, v___x_5341_);
v___x_5343_ = l_Lean_Syntax_node2(v___x_5319_, v___x_5321_, v___x_5339_, v___x_5342_);
v___x_5344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5346_, 0, v___x_5319_);
lean_ctor_set(v___x_5346_, 1, v___x_5345_);
v___x_5347_ = l_Lean_Syntax_node2(v___x_5319_, v___x_5344_, v___x_5346_, v_b_5303_);
v___x_5348_ = l_Lean_Syntax_node2(v___x_5319_, v___x_5321_, v___x_5347_, v___x_5329_);
v___x_5349_ = l_Lean_Syntax_node2(v___x_5319_, v___x_5320_, v___x_5343_, v___x_5348_);
v___x_5350_ = l_Lean_Syntax_node1(v___x_5319_, v___x_5316_, v___x_5349_);
v___x_5351_ = ((size_t)1ULL);
v___x_5352_ = lean_usize_add(v_i_5302_, v___x_5351_);
v___x_5353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5300_, v_sz_5301_, v___x_5352_, v___x_5350_, v___y_5309_);
return v___x_5353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5354_, lean_object* v_sz_5355_, lean_object* v_i_5356_, lean_object* v_b_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
size_t v_sz_boxed_5366_; size_t v_i_boxed_5367_; lean_object* v_res_5368_; 
v_sz_boxed_5366_ = lean_unbox_usize(v_sz_5355_);
lean_dec(v_sz_5355_);
v_i_boxed_5367_ = lean_unbox_usize(v_i_5356_);
lean_dec(v_i_5356_);
v_res_5368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5354_, v_sz_boxed_5366_, v_i_boxed_5367_, v_b_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec_ref(v_as_5354_);
return v_res_5368_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5408_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5409_ = l_String_toRawSubstring_x27(v___x_5408_);
return v___x_5409_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5423_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5424_ = l_String_toRawSubstring_x27(v___x_5423_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5441_, lean_object* v_dec_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v___x_5451_; uint8_t v___x_5452_; 
v___x_5451_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5441_);
v___x_5452_ = l_Lean_Syntax_isOfKind(v_stx_5441_, v___x_5451_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; 
lean_dec_ref(v_dec_5442_);
lean_dec(v_stx_5441_);
v___x_5453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5453_;
}
else
{
lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; uint8_t v___y_5459_; lean_object* v_body_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5541_; lean_object* v___y_5542_; uint8_t v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; uint8_t v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v_a_5556_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; uint8_t v___y_5573_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v_mutTk_x3f_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5658_; lean_object* v___y_5659_; lean_object* v___y_5660_; lean_object* v___y_5661_; lean_object* v___y_5662_; lean_object* v___x_5686_; lean_object* v___x_5687_; uint8_t v___x_5688_; 
v___x_5686_ = lean_unsigned_to_nat(1u);
v___x_5687_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5686_);
v___x_5688_ = l_Lean_Syntax_isNone(v___x_5687_);
if (v___x_5688_ == 0)
{
uint8_t v___x_5689_; 
lean_inc(v___x_5687_);
v___x_5689_ = l_Lean_Syntax_matchesNull(v___x_5687_, v___x_5686_);
if (v___x_5689_ == 0)
{
lean_object* v___x_5690_; 
lean_dec(v___x_5687_);
lean_dec_ref(v_dec_5442_);
lean_dec(v_stx_5441_);
v___x_5690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5690_;
}
else
{
lean_object* v___x_5691_; lean_object* v_mutTk_x3f_5692_; lean_object* v___x_5693_; 
v___x_5691_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5692_ = l_Lean_Syntax_getArg(v___x_5687_, v___x_5691_);
lean_dec(v___x_5687_);
v___x_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5693_, 0, v_mutTk_x3f_5692_);
v_mutTk_x3f_5655_ = v___x_5693_;
v___y_5656_ = v_a_5443_;
v___y_5657_ = v_a_5444_;
v___y_5658_ = v_a_5445_;
v___y_5659_ = v_a_5446_;
v___y_5660_ = v_a_5447_;
v___y_5661_ = v_a_5448_;
v___y_5662_ = v_a_5449_;
goto v___jp_5654_;
}
}
else
{
lean_object* v___x_5694_; 
lean_dec(v___x_5687_);
v___x_5694_ = lean_box(0);
v_mutTk_x3f_5655_ = v___x_5694_;
v___y_5656_ = v_a_5443_;
v___y_5657_ = v_a_5444_;
v___y_5658_ = v_a_5445_;
v___y_5659_ = v_a_5446_;
v___y_5660_ = v_a_5447_;
v___y_5661_ = v_a_5448_;
v___y_5662_ = v_a_5449_;
goto v___jp_5654_;
}
v___jp_5454_:
{
lean_object* v_eq_x3f_5468_; 
v_eq_x3f_5468_ = lean_ctor_get(v___y_5456_, 0);
lean_inc(v_eq_x3f_5468_);
lean_dec_ref(v___y_5456_);
if (lean_obj_tag(v_eq_x3f_5468_) == 1)
{
lean_object* v_val_5469_; lean_object* v_ref_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; 
v_val_5469_ = lean_ctor_get(v_eq_x3f_5468_, 0);
lean_inc(v_val_5469_);
lean_dec_ref_known(v_eq_x3f_5468_, 1);
v_ref_5470_ = lean_ctor_get(v___y_5466_, 5);
v___x_5471_ = l_Lean_SourceInfo_fromRef(v_ref_5470_, v___y_5459_);
v___x_5472_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5473_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5471_, 19);
v___x_5474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5471_);
lean_ctor_set(v___x_5474_, 1, v___x_5473_);
v___x_5475_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5476_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5471_);
lean_ctor_set(v___x_5477_, 1, v___x_5475_);
lean_ctor_set(v___x_5477_, 2, v___x_5476_);
v___x_5478_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5479_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5471_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = l_Lean_Syntax_node2(v___x_5471_, v___x_5475_, v_val_5469_, v___x_5480_);
v___x_5482_ = l_Lean_Syntax_node2(v___x_5471_, v___x_5478_, v___x_5481_, v___y_5455_);
v___x_5483_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5475_, v___x_5482_);
v___x_5484_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5471_);
lean_ctor_set(v___x_5485_, 1, v___x_5484_);
v___x_5486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5487_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5488_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5471_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5475_, v___y_5457_);
v___x_5491_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5475_, v___x_5490_);
v___x_5492_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5471_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
lean_inc_ref(v___x_5493_);
lean_inc_ref(v___x_5489_);
v___x_5494_ = l_Lean_Syntax_node4(v___x_5471_, v___x_5487_, v___x_5489_, v___x_5491_, v___x_5493_, v_body_5460_);
v___x_5495_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5496_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5471_);
lean_ctor_set(v___x_5497_, 1, v___x_5496_);
v___x_5498_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5495_, v___x_5497_);
v___x_5499_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5475_, v___x_5498_);
v___x_5500_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5475_, v___x_5499_);
v___x_5501_ = l_Lean_Syntax_node4(v___x_5471_, v___x_5487_, v___x_5489_, v___x_5500_, v___x_5493_, v___y_5458_);
v___x_5502_ = l_Lean_Syntax_node2(v___x_5471_, v___x_5475_, v___x_5494_, v___x_5501_);
v___x_5503_ = l_Lean_Syntax_node1(v___x_5471_, v___x_5486_, v___x_5502_);
lean_inc_ref_n(v___x_5477_, 2);
v___x_5504_ = l_Lean_Syntax_node7(v___x_5471_, v___x_5472_, v___x_5474_, v___x_5477_, v___x_5477_, v___x_5477_, v___x_5483_, v___x_5485_, v___x_5503_);
v___x_5505_ = l_Lean_Elab_Do_elabDoElem(v___x_5504_, v_dec_5442_, v___x_5452_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
return v___x_5505_;
}
else
{
lean_object* v_ref_5506_; lean_object* v___x_5507_; lean_object* v_a_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_dec(v_eq_x3f_5468_);
v_ref_5506_ = lean_ctor_get(v___y_5466_, 5);
v___x_5507_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5506_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc_n(v_a_5508_, 18);
lean_dec_ref(v___x_5507_);
v___x_5509_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5511_, 0, v_a_5508_);
lean_ctor_set(v___x_5511_, 1, v___x_5510_);
v___x_5512_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5513_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5514_, 0, v_a_5508_);
lean_ctor_set(v___x_5514_, 1, v___x_5512_);
lean_ctor_set(v___x_5514_, 2, v___x_5513_);
v___x_5515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5514_, 3);
v___x_5516_ = l_Lean_Syntax_node2(v_a_5508_, v___x_5515_, v___x_5514_, v___y_5455_);
v___x_5517_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5512_, v___x_5516_);
v___x_5518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5519_, 0, v_a_5508_);
lean_ctor_set(v___x_5519_, 1, v___x_5518_);
v___x_5520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5521_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5522_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5523_, 0, v_a_5508_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
v___x_5524_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5512_, v___y_5457_);
v___x_5525_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5512_, v___x_5524_);
v___x_5526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5527_, 0, v_a_5508_);
lean_ctor_set(v___x_5527_, 1, v___x_5526_);
lean_inc_ref(v___x_5527_);
lean_inc_ref(v___x_5523_);
v___x_5528_ = l_Lean_Syntax_node4(v_a_5508_, v___x_5521_, v___x_5523_, v___x_5525_, v___x_5527_, v_body_5460_);
v___x_5529_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5531_, 0, v_a_5508_);
lean_ctor_set(v___x_5531_, 1, v___x_5530_);
v___x_5532_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5529_, v___x_5531_);
v___x_5533_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5512_, v___x_5532_);
v___x_5534_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5512_, v___x_5533_);
v___x_5535_ = l_Lean_Syntax_node4(v_a_5508_, v___x_5521_, v___x_5523_, v___x_5534_, v___x_5527_, v___y_5458_);
v___x_5536_ = l_Lean_Syntax_node2(v_a_5508_, v___x_5512_, v___x_5528_, v___x_5535_);
v___x_5537_ = l_Lean_Syntax_node1(v_a_5508_, v___x_5520_, v___x_5536_);
v___x_5538_ = l_Lean_Syntax_node7(v_a_5508_, v___x_5509_, v___x_5511_, v___x_5514_, v___x_5514_, v___x_5514_, v___x_5517_, v___x_5519_, v___x_5537_);
v___x_5539_ = l_Lean_Elab_Do_elabDoElem(v___x_5538_, v_dec_5442_, v___x_5452_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
return v___x_5539_;
}
}
v___jp_5540_:
{
if (lean_obj_tag(v___y_5555_) == 0)
{
lean_dec_ref(v___y_5547_);
v___y_5455_ = v___y_5548_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5550_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
v_body_5460_ = v_a_5556_;
v___y_5461_ = v___y_5541_;
v___y_5462_ = v___y_5542_;
v___y_5463_ = v___y_5544_;
v___y_5464_ = v___y_5554_;
v___y_5465_ = v___y_5553_;
v___y_5466_ = v___y_5551_;
v___y_5467_ = v___y_5552_;
goto v___jp_5454_;
}
else
{
lean_dec_ref_known(v___y_5555_, 1);
if (v___y_5543_ == 0)
{
lean_dec_ref(v___y_5547_);
v___y_5455_ = v___y_5548_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5550_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
v_body_5460_ = v_a_5556_;
v___y_5461_ = v___y_5541_;
v___y_5462_ = v___y_5542_;
v___y_5463_ = v___y_5544_;
v___y_5464_ = v___y_5554_;
v___y_5465_ = v___y_5553_;
v___y_5466_ = v___y_5551_;
v___y_5467_ = v___y_5552_;
goto v___jp_5454_;
}
else
{
size_t v_sz_5557_; size_t v___x_5558_; lean_object* v___x_5559_; 
v_sz_5557_ = lean_array_size(v___y_5547_);
v___x_5558_ = ((size_t)0ULL);
v___x_5559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5547_, v_sz_5557_, v___x_5558_, v_a_5556_, v___y_5541_, v___y_5542_, v___y_5544_, v___y_5554_, v___y_5553_, v___y_5551_, v___y_5552_);
lean_dec_ref(v___y_5547_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref_known(v___x_5559_, 1);
v___y_5455_ = v___y_5548_;
v___y_5456_ = v___y_5549_;
v___y_5457_ = v___y_5550_;
v___y_5458_ = v___y_5545_;
v___y_5459_ = v___y_5546_;
v_body_5460_ = v_a_5560_;
v___y_5461_ = v___y_5541_;
v___y_5462_ = v___y_5542_;
v___y_5463_ = v___y_5544_;
v___y_5464_ = v___y_5554_;
v___y_5465_ = v___y_5553_;
v___y_5466_ = v___y_5551_;
v___y_5467_ = v___y_5552_;
goto v___jp_5454_;
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5568_; 
lean_dec(v___y_5550_);
lean_dec_ref(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec_ref(v_dec_5442_);
v_a_5561_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5563_ = v___x_5559_;
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5559_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
}
}
v___jp_5569_:
{
uint8_t v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5584_ = 0;
v___x_5585_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5586_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5570_, v___y_5582_, v___x_5585_, v___y_5572_, v___y_5575_, v___y_5581_, v___y_5580_, v___y_5578_, v___y_5579_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v_a_5587_; lean_object* v___x_5588_; 
v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc(v_a_5587_);
lean_dec_ref_known(v___x_5586_, 1);
v___x_5588_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5587_, v___y_5571_, v___y_5572_, v___y_5575_, v___y_5581_, v___y_5580_, v___y_5578_, v___y_5579_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v___x_5589_; 
lean_dec_ref_known(v___x_5588_, 1);
lean_inc(v___y_5577_);
v___x_5589_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5577_, v___y_5572_, v___y_5575_, v___y_5581_, v___y_5580_, v___y_5578_, v___y_5579_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_a_5590_);
lean_dec_ref_known(v___x_5589_, 1);
lean_inc(v___y_5582_);
v___x_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5591_, 0, v___y_5582_);
v___x_5592_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5591_, v_a_5590_, v___y_5571_, v___y_5572_, v___y_5575_, v___y_5581_, v___y_5580_, v___y_5578_, v___y_5579_);
lean_dec_ref_known(v___x_5591_, 1);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_dec_ref_known(v___x_5592_, 1);
if (lean_obj_tag(v___y_5583_) == 0)
{
lean_object* v_ref_5593_; lean_object* v_quotContext_5594_; lean_object* v_currMacroScope_5595_; lean_object* v___x_5596_; lean_object* v_a_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; 
v_ref_5593_ = lean_ctor_get(v___y_5578_, 5);
v_quotContext_5594_ = lean_ctor_get(v___y_5578_, 10);
v_currMacroScope_5595_ = lean_ctor_get(v___y_5578_, 11);
v___x_5596_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5593_, v___y_5571_, v___y_5572_, v___y_5575_, v___y_5581_, v___y_5580_, v___y_5578_, v___y_5579_);
v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
lean_inc_n(v_a_5597_, 9);
lean_dec_ref(v___x_5596_);
v___x_5598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5599_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5601_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5602_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5603_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5604_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5595_, 2);
lean_inc_n(v_quotContext_5594_, 2);
v___x_5605_ = l_Lean_addMacroScope(v_quotContext_5594_, v___x_5604_, v_currMacroScope_5595_);
v___x_5606_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5607_, 0, v_a_5597_);
lean_ctor_set(v___x_5607_, 1, v___x_5603_);
lean_ctor_set(v___x_5607_, 2, v___x_5605_);
lean_ctor_set(v___x_5607_, 3, v___x_5606_);
v___x_5608_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5610_ = l_Lean_addMacroScope(v_quotContext_5594_, v___x_5609_, v_currMacroScope_5595_);
v___x_5611_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5612_, 0, v_a_5597_);
lean_ctor_set(v___x_5612_, 1, v___x_5608_);
lean_ctor_set(v___x_5612_, 2, v___x_5610_);
lean_ctor_set(v___x_5612_, 3, v___x_5611_);
v___x_5613_ = l_Lean_Syntax_node1(v_a_5597_, v___x_5599_, v___x_5612_);
v___x_5614_ = l_Lean_Syntax_node2(v_a_5597_, v___x_5602_, v___x_5607_, v___x_5613_);
v___x_5615_ = l_Lean_Syntax_node1(v_a_5597_, v___x_5601_, v___x_5614_);
v___x_5616_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5617_, 0, v_a_5597_);
lean_ctor_set(v___x_5617_, 1, v___x_5599_);
lean_ctor_set(v___x_5617_, 2, v___x_5616_);
v___x_5618_ = l_Lean_Syntax_node2(v_a_5597_, v___x_5600_, v___x_5615_, v___x_5617_);
v___x_5619_ = l_Lean_Syntax_node1(v_a_5597_, v___x_5599_, v___x_5618_);
v___x_5620_ = l_Lean_Syntax_node1(v_a_5597_, v___x_5598_, v___x_5619_);
v___y_5541_ = v___y_5571_;
v___y_5542_ = v___y_5572_;
v___y_5543_ = v___y_5573_;
v___y_5544_ = v___y_5575_;
v___y_5545_ = v___y_5574_;
v___y_5546_ = v___x_5584_;
v___y_5547_ = v_a_5590_;
v___y_5548_ = v___y_5576_;
v___y_5549_ = v_a_5587_;
v___y_5550_ = v___y_5577_;
v___y_5551_ = v___y_5578_;
v___y_5552_ = v___y_5579_;
v___y_5553_ = v___y_5580_;
v___y_5554_ = v___y_5581_;
v___y_5555_ = v___y_5582_;
v_a_5556_ = v___x_5620_;
goto v___jp_5540_;
}
else
{
lean_object* v_val_5621_; 
v_val_5621_ = lean_ctor_get(v___y_5583_, 0);
lean_inc(v_val_5621_);
lean_dec_ref_known(v___y_5583_, 1);
v___y_5541_ = v___y_5571_;
v___y_5542_ = v___y_5572_;
v___y_5543_ = v___y_5573_;
v___y_5544_ = v___y_5575_;
v___y_5545_ = v___y_5574_;
v___y_5546_ = v___x_5584_;
v___y_5547_ = v_a_5590_;
v___y_5548_ = v___y_5576_;
v___y_5549_ = v_a_5587_;
v___y_5550_ = v___y_5577_;
v___y_5551_ = v___y_5578_;
v___y_5552_ = v___y_5579_;
v___y_5553_ = v___y_5580_;
v___y_5554_ = v___y_5581_;
v___y_5555_ = v___y_5582_;
v_a_5556_ = v_val_5621_;
goto v___jp_5540_;
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_dec(v_a_5590_);
lean_dec(v_a_5587_);
lean_dec(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec_ref(v_dec_5442_);
v_a_5622_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5592_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5592_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
else
{
lean_object* v_a_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5637_; 
lean_dec(v_a_5587_);
lean_dec(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec_ref(v_dec_5442_);
v_a_5630_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5637_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5632_ = v___x_5589_;
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_a_5630_);
lean_dec(v___x_5589_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5635_; 
if (v_isShared_5633_ == 0)
{
v___x_5635_ = v___x_5632_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_a_5630_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
else
{
lean_object* v_a_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5645_; 
lean_dec(v_a_5587_);
lean_dec(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec_ref(v_dec_5442_);
v_a_5638_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5640_ = v___x_5588_;
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
else
{
lean_inc(v_a_5638_);
lean_dec(v___x_5588_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v___x_5643_; 
if (v_isShared_5641_ == 0)
{
v___x_5643_ = v___x_5640_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_a_5638_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
lean_dec(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec_ref(v_dec_5442_);
v_a_5646_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5586_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5586_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5646_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
v___jp_5654_:
{
lean_object* v___x_5663_; lean_object* v_cfg_5664_; lean_object* v___x_5665_; uint8_t v___x_5666_; 
v___x_5663_ = lean_unsigned_to_nat(2u);
v_cfg_5664_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5663_);
v___x_5665_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5664_);
v___x_5666_ = l_Lean_Syntax_isOfKind(v_cfg_5664_, v___x_5665_);
if (v___x_5666_ == 0)
{
lean_object* v___x_5667_; 
lean_dec(v_cfg_5664_);
lean_dec(v_mutTk_x3f_5655_);
lean_dec_ref(v_dec_5442_);
lean_dec(v_stx_5441_);
v___x_5667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5667_;
}
else
{
lean_object* v___x_5668_; lean_object* v_pattern_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v___x_5668_ = lean_unsigned_to_nat(3u);
v_pattern_5669_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5668_);
v___x_5670_ = lean_unsigned_to_nat(5u);
v___x_5671_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5670_);
v___x_5672_ = lean_unsigned_to_nat(7u);
v___x_5673_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5672_);
v___x_5674_ = lean_unsigned_to_nat(8u);
v___x_5675_ = l_Lean_Syntax_getArg(v_stx_5441_, v___x_5674_);
lean_dec(v_stx_5441_);
v___x_5676_ = l_Lean_Syntax_getOptional_x3f(v___x_5675_);
lean_dec(v___x_5675_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_object* v___x_5677_; 
v___x_5677_ = lean_box(0);
v___y_5570_ = v_cfg_5664_;
v___y_5571_ = v___y_5656_;
v___y_5572_ = v___y_5657_;
v___y_5573_ = v___x_5666_;
v___y_5574_ = v___x_5673_;
v___y_5575_ = v___y_5658_;
v___y_5576_ = v___x_5671_;
v___y_5577_ = v_pattern_5669_;
v___y_5578_ = v___y_5661_;
v___y_5579_ = v___y_5662_;
v___y_5580_ = v___y_5660_;
v___y_5581_ = v___y_5659_;
v___y_5582_ = v_mutTk_x3f_5655_;
v___y_5583_ = v___x_5677_;
goto v___jp_5569_;
}
else
{
lean_object* v_val_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5685_; 
v_val_5678_ = lean_ctor_get(v___x_5676_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v___x_5676_);
if (v_isSharedCheck_5685_ == 0)
{
v___x_5680_ = v___x_5676_;
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_val_5678_);
lean_dec(v___x_5676_);
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
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_val_5678_);
v___x_5683_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
v___y_5570_ = v_cfg_5664_;
v___y_5571_ = v___y_5656_;
v___y_5572_ = v___y_5657_;
v___y_5573_ = v___x_5666_;
v___y_5574_ = v___x_5673_;
v___y_5575_ = v___y_5658_;
v___y_5576_ = v___x_5671_;
v___y_5577_ = v_pattern_5669_;
v___y_5578_ = v___y_5661_;
v___y_5579_ = v___y_5662_;
v___y_5580_ = v___y_5660_;
v___y_5581_ = v___y_5659_;
v___y_5582_ = v_mutTk_x3f_5655_;
v___y_5583_ = v___x_5683_;
goto v___jp_5569_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5695_, lean_object* v_dec_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5695_, v_dec_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_a_5701_);
lean_dec_ref(v_a_5700_);
lean_dec(v_a_5699_);
lean_dec_ref(v_a_5698_);
lean_dec_ref(v_a_5697_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5706_, size_t v_sz_5707_, size_t v_i_5708_, lean_object* v_b_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5706_, v_sz_5707_, v_i_5708_, v_b_5709_, v___y_5715_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5719_, lean_object* v_sz_5720_, lean_object* v_i_5721_, lean_object* v_b_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
size_t v_sz_boxed_5731_; size_t v_i_boxed_5732_; lean_object* v_res_5733_; 
v_sz_boxed_5731_ = lean_unbox_usize(v_sz_5720_);
lean_dec(v_sz_5720_);
v_i_boxed_5732_ = lean_unbox_usize(v_i_5721_);
lean_dec(v_i_5721_);
v_res_5733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5719_, v_sz_boxed_5731_, v_i_boxed_5732_, v_b_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec_ref(v_as_5719_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5741_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5742_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5743_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5744_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5745_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5741_, v___x_5742_, v___x_5743_, v___x_5744_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5746_){
_start:
{
lean_object* v_res_5747_; 
v_res_5747_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5747_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5755_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5756_ = l_Lean_stringToMessageData(v___x_5755_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5757_, lean_object* v_dec_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v___x_5767_; uint8_t v___x_5768_; 
v___x_5767_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5757_);
v___x_5768_ = l_Lean_Syntax_isOfKind(v_stx_5757_, v___x_5767_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; 
lean_dec_ref(v_dec_5758_);
lean_dec(v_stx_5757_);
v___x_5769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5769_;
}
else
{
lean_object* v___x_5770_; lean_object* v_tk_5771_; lean_object* v___y_5773_; lean_object* v___y_5774_; lean_object* v___y_5775_; lean_object* v___y_5776_; lean_object* v___y_5777_; lean_object* v___y_5778_; lean_object* v___y_5779_; lean_object* v___y_5780_; lean_object* v___y_5781_; lean_object* v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v___y_5794_; lean_object* v___y_5806_; lean_object* v___y_5807_; uint8_t v___y_5808_; lean_object* v___y_5809_; lean_object* v___y_5810_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; uint8_t v___y_5818_; lean_object* v___y_5821_; lean_object* v___y_5822_; uint8_t v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; uint8_t v___y_5833_; lean_object* v_mutTk_x3f_5836_; lean_object* v___y_5837_; lean_object* v___y_5838_; lean_object* v___y_5839_; lean_object* v___y_5840_; lean_object* v___y_5841_; lean_object* v___y_5842_; lean_object* v___y_5843_; lean_object* v___x_5873_; lean_object* v___x_5874_; uint8_t v___x_5875_; 
v___x_5770_ = lean_unsigned_to_nat(0u);
v_tk_5771_ = l_Lean_Syntax_getArg(v_stx_5757_, v___x_5770_);
v___x_5873_ = lean_unsigned_to_nat(1u);
v___x_5874_ = l_Lean_Syntax_getArg(v_stx_5757_, v___x_5873_);
v___x_5875_ = l_Lean_Syntax_isNone(v___x_5874_);
if (v___x_5875_ == 0)
{
uint8_t v___x_5876_; 
lean_inc(v___x_5874_);
v___x_5876_ = l_Lean_Syntax_matchesNull(v___x_5874_, v___x_5873_);
if (v___x_5876_ == 0)
{
lean_object* v___x_5877_; 
lean_dec(v___x_5874_);
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
lean_dec(v_stx_5757_);
v___x_5877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5877_;
}
else
{
lean_object* v_mutTk_x3f_5878_; lean_object* v___x_5879_; 
v_mutTk_x3f_5878_ = l_Lean_Syntax_getArg(v___x_5874_, v___x_5770_);
lean_dec(v___x_5874_);
v___x_5879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5879_, 0, v_mutTk_x3f_5878_);
v_mutTk_x3f_5836_ = v___x_5879_;
v___y_5837_ = v_a_5759_;
v___y_5838_ = v_a_5760_;
v___y_5839_ = v_a_5761_;
v___y_5840_ = v_a_5762_;
v___y_5841_ = v_a_5763_;
v___y_5842_ = v_a_5764_;
v___y_5843_ = v_a_5765_;
goto v___jp_5835_;
}
}
else
{
lean_object* v___x_5880_; 
lean_dec(v___x_5874_);
v___x_5880_ = lean_box(0);
v_mutTk_x3f_5836_ = v___x_5880_;
v___y_5837_ = v_a_5759_;
v___y_5838_ = v_a_5760_;
v___y_5839_ = v_a_5761_;
v___y_5840_ = v_a_5762_;
v___y_5841_ = v_a_5763_;
v___y_5842_ = v_a_5764_;
v___y_5843_ = v_a_5765_;
goto v___jp_5835_;
}
v___jp_5772_:
{
lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5782_, 0, v___y_5773_);
v___x_5783_ = l_Lean_Elab_Do_elabDoArrow(v___x_5782_, v___y_5774_, v_tk_5771_, v_dec_5758_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
lean_dec(v_tk_5771_);
return v___x_5783_;
}
v___jp_5784_:
{
lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
lean_dec(v___y_5792_);
lean_dec(v___y_5791_);
v___x_5795_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5796_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5788_, v___x_5795_, v___y_5785_, v___y_5786_, v___y_5794_, v___y_5793_);
lean_dec(v___y_5788_);
v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5796_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5796_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
v___jp_5805_:
{
if (v___y_5818_ == 0)
{
lean_object* v_eq_x3f_5819_; 
v_eq_x3f_5819_ = lean_ctor_get(v___y_5817_, 0);
lean_inc(v_eq_x3f_5819_);
lean_dec_ref(v___y_5817_);
if (lean_obj_tag(v_eq_x3f_5819_) == 0)
{
lean_dec(v___y_5815_);
v___y_5773_ = v___y_5813_;
v___y_5774_ = v___y_5816_;
v___y_5775_ = v___y_5814_;
v___y_5776_ = v___y_5812_;
v___y_5777_ = v___y_5810_;
v___y_5778_ = v___y_5806_;
v___y_5779_ = v___y_5807_;
v___y_5780_ = v___y_5811_;
v___y_5781_ = v___y_5809_;
goto v___jp_5772_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5819_, 1);
if (v___y_5808_ == 0)
{
lean_dec(v___y_5815_);
v___y_5773_ = v___y_5813_;
v___y_5774_ = v___y_5816_;
v___y_5775_ = v___y_5814_;
v___y_5776_ = v___y_5812_;
v___y_5777_ = v___y_5810_;
v___y_5778_ = v___y_5806_;
v___y_5779_ = v___y_5807_;
v___y_5780_ = v___y_5811_;
v___y_5781_ = v___y_5809_;
goto v___jp_5772_;
}
else
{
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
v___y_5785_ = v___y_5806_;
v___y_5786_ = v___y_5807_;
v___y_5787_ = v___y_5812_;
v___y_5788_ = v___y_5815_;
v___y_5789_ = v___y_5814_;
v___y_5790_ = v___y_5810_;
v___y_5791_ = v___y_5813_;
v___y_5792_ = v___y_5816_;
v___y_5793_ = v___y_5809_;
v___y_5794_ = v___y_5811_;
goto v___jp_5784_;
}
}
}
else
{
lean_dec_ref(v___y_5817_);
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
v___y_5785_ = v___y_5806_;
v___y_5786_ = v___y_5807_;
v___y_5787_ = v___y_5812_;
v___y_5788_ = v___y_5815_;
v___y_5789_ = v___y_5814_;
v___y_5790_ = v___y_5810_;
v___y_5791_ = v___y_5813_;
v___y_5792_ = v___y_5816_;
v___y_5793_ = v___y_5809_;
v___y_5794_ = v___y_5811_;
goto v___jp_5784_;
}
}
v___jp_5820_:
{
if (v___y_5833_ == 0)
{
uint8_t v_zeta_5834_; 
v_zeta_5834_ = lean_ctor_get_uint8(v___y_5832_, sizeof(void*)*1 + 2);
v___y_5806_ = v___y_5821_;
v___y_5807_ = v___y_5822_;
v___y_5808_ = v___y_5823_;
v___y_5809_ = v___y_5824_;
v___y_5810_ = v___y_5825_;
v___y_5811_ = v___y_5826_;
v___y_5812_ = v___y_5827_;
v___y_5813_ = v___y_5828_;
v___y_5814_ = v___y_5829_;
v___y_5815_ = v___y_5830_;
v___y_5816_ = v___y_5831_;
v___y_5817_ = v___y_5832_;
v___y_5818_ = v_zeta_5834_;
goto v___jp_5805_;
}
else
{
v___y_5806_ = v___y_5821_;
v___y_5807_ = v___y_5822_;
v___y_5808_ = v___y_5823_;
v___y_5809_ = v___y_5824_;
v___y_5810_ = v___y_5825_;
v___y_5811_ = v___y_5826_;
v___y_5812_ = v___y_5827_;
v___y_5813_ = v___y_5828_;
v___y_5814_ = v___y_5829_;
v___y_5815_ = v___y_5830_;
v___y_5816_ = v___y_5831_;
v___y_5817_ = v___y_5832_;
v___y_5818_ = v___x_5768_;
goto v___jp_5805_;
}
}
v___jp_5835_:
{
lean_object* v___x_5844_; lean_object* v_cfg_5845_; lean_object* v___x_5846_; uint8_t v___x_5847_; 
v___x_5844_ = lean_unsigned_to_nat(2u);
v_cfg_5845_ = l_Lean_Syntax_getArg(v_stx_5757_, v___x_5844_);
v___x_5846_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5845_);
v___x_5847_ = l_Lean_Syntax_isOfKind(v_cfg_5845_, v___x_5846_);
if (v___x_5847_ == 0)
{
lean_object* v___x_5848_; 
lean_dec(v_cfg_5845_);
lean_dec(v_mutTk_x3f_5836_);
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
lean_dec(v_stx_5757_);
v___x_5848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5848_;
}
else
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5845_);
v___x_5850_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5845_, v_mutTk_x3f_5836_, v___x_5849_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5850_) == 0)
{
lean_object* v_a_5851_; lean_object* v___x_5852_; 
v_a_5851_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5851_);
lean_dec_ref_known(v___x_5850_, 1);
v___x_5852_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5851_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5852_) == 0)
{
uint8_t v_nondep_5853_; uint8_t v_usedOnly_5854_; lean_object* v___x_5855_; lean_object* v_decl_5856_; 
lean_dec_ref_known(v___x_5852_, 1);
v_nondep_5853_ = lean_ctor_get_uint8(v_a_5851_, sizeof(void*)*1);
v_usedOnly_5854_ = lean_ctor_get_uint8(v_a_5851_, sizeof(void*)*1 + 1);
v___x_5855_ = lean_unsigned_to_nat(3u);
v_decl_5856_ = l_Lean_Syntax_getArg(v_stx_5757_, v___x_5855_);
lean_dec(v_stx_5757_);
if (v_nondep_5853_ == 0)
{
v___y_5821_ = v___y_5840_;
v___y_5822_ = v___y_5841_;
v___y_5823_ = v___x_5847_;
v___y_5824_ = v___y_5843_;
v___y_5825_ = v___y_5839_;
v___y_5826_ = v___y_5842_;
v___y_5827_ = v___y_5838_;
v___y_5828_ = v_mutTk_x3f_5836_;
v___y_5829_ = v___y_5837_;
v___y_5830_ = v_cfg_5845_;
v___y_5831_ = v_decl_5856_;
v___y_5832_ = v_a_5851_;
v___y_5833_ = v_usedOnly_5854_;
goto v___jp_5820_;
}
else
{
v___y_5821_ = v___y_5840_;
v___y_5822_ = v___y_5841_;
v___y_5823_ = v___x_5847_;
v___y_5824_ = v___y_5843_;
v___y_5825_ = v___y_5839_;
v___y_5826_ = v___y_5842_;
v___y_5827_ = v___y_5838_;
v___y_5828_ = v_mutTk_x3f_5836_;
v___y_5829_ = v___y_5837_;
v___y_5830_ = v_cfg_5845_;
v___y_5831_ = v_decl_5856_;
v___y_5832_ = v_a_5851_;
v___y_5833_ = v___x_5768_;
goto v___jp_5820_;
}
}
else
{
lean_object* v_a_5857_; lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5864_; 
lean_dec(v_a_5851_);
lean_dec(v_cfg_5845_);
lean_dec(v_mutTk_x3f_5836_);
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
lean_dec(v_stx_5757_);
v_a_5857_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5864_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5859_ = v___x_5852_;
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
else
{
lean_inc(v_a_5857_);
lean_dec(v___x_5852_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
lean_object* v___x_5862_; 
if (v_isShared_5860_ == 0)
{
v___x_5862_ = v___x_5859_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
v___x_5862_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5861_;
}
v_reusejp_5861_:
{
return v___x_5862_;
}
}
}
}
else
{
lean_object* v_a_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5872_; 
lean_dec(v_cfg_5845_);
lean_dec(v_mutTk_x3f_5836_);
lean_dec(v_tk_5771_);
lean_dec_ref(v_dec_5758_);
lean_dec(v_stx_5757_);
v_a_5865_ = lean_ctor_get(v___x_5850_, 0);
v_isSharedCheck_5872_ = !lean_is_exclusive(v___x_5850_);
if (v_isSharedCheck_5872_ == 0)
{
v___x_5867_ = v___x_5850_;
v_isShared_5868_ = v_isSharedCheck_5872_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_a_5865_);
lean_dec(v___x_5850_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5872_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5870_; 
if (v_isShared_5868_ == 0)
{
v___x_5870_ = v___x_5867_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_a_5865_);
v___x_5870_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
return v___x_5870_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5881_, lean_object* v_dec_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_){
_start:
{
lean_object* v_res_5891_; 
v_res_5891_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5881_, v_dec_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
lean_dec(v_a_5889_);
lean_dec_ref(v_a_5888_);
lean_dec(v_a_5887_);
lean_dec_ref(v_a_5886_);
lean_dec(v_a_5885_);
lean_dec_ref(v_a_5884_);
lean_dec_ref(v_a_5883_);
return v_res_5891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; 
v___x_5899_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5900_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5901_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5902_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5903_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5899_, v___x_5900_, v___x_5901_, v___x_5902_);
return v___x_5903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5904_){
_start:
{
lean_object* v_res_5905_; 
v_res_5905_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5912_, lean_object* v_dec_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_){
_start:
{
lean_object* v___x_5922_; uint8_t v___x_5923_; 
v___x_5922_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5912_);
v___x_5923_ = l_Lean_Syntax_isOfKind(v_stx_5912_, v___x_5922_);
if (v___x_5923_ == 0)
{
lean_object* v___x_5924_; 
lean_dec_ref(v_dec_5913_);
lean_dec(v_stx_5912_);
v___x_5924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5924_;
}
else
{
lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; uint8_t v___x_5928_; 
v___x_5925_ = lean_unsigned_to_nat(0u);
v___x_5926_ = l_Lean_Syntax_getArg(v_stx_5912_, v___x_5925_);
lean_dec(v_stx_5912_);
v___x_5927_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5926_);
v___x_5928_ = l_Lean_Syntax_isOfKind(v___x_5926_, v___x_5927_);
if (v___x_5928_ == 0)
{
lean_object* v___x_5929_; uint8_t v___x_5930_; 
v___x_5929_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5926_);
v___x_5930_ = l_Lean_Syntax_isOfKind(v___x_5926_, v___x_5929_);
if (v___x_5930_ == 0)
{
lean_object* v___x_5931_; 
lean_dec(v___x_5926_);
lean_dec_ref(v_dec_5913_);
v___x_5931_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5931_;
}
else
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = lean_box(2);
lean_inc(v___x_5926_);
v___x_5933_ = l_Lean_Elab_Do_elabDoArrow(v___x_5932_, v___x_5926_, v___x_5926_, v_dec_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_);
lean_dec(v___x_5926_);
return v___x_5933_;
}
}
else
{
lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5934_ = lean_box(2);
lean_inc(v___x_5926_);
v___x_5935_ = l_Lean_Elab_Do_elabDoArrow(v___x_5934_, v___x_5926_, v___x_5926_, v_dec_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_);
lean_dec(v___x_5926_);
return v___x_5935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5936_, lean_object* v_dec_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
lean_object* v_res_5946_; 
v_res_5946_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5936_, v_dec_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_);
lean_dec(v_a_5944_);
lean_dec_ref(v_a_5943_);
lean_dec(v_a_5942_);
lean_dec_ref(v_a_5941_);
lean_dec(v_a_5940_);
lean_dec_ref(v_a_5939_);
lean_dec_ref(v_a_5938_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5954_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5955_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5956_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5957_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5958_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5954_, v___x_5955_, v___x_5956_, v___x_5957_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5960_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
