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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_304_; lean_object* v_env_305_; lean_object* v___x_306_; lean_object* v_toCold_307_; lean_object* v_mctx_308_; lean_object* v_lctx_309_; lean_object* v_options_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_304_ = lean_st_ref_get(v___y_302_);
v_env_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_env_305_);
lean_dec(v___x_304_);
v___x_306_ = lean_st_ref_get(v___y_300_);
v_toCold_307_ = lean_ctor_get(v___y_301_, 0);
v_mctx_308_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_mctx_308_);
lean_dec(v___x_306_);
v_lctx_309_ = lean_ctor_get(v___y_299_, 2);
v_options_310_ = lean_ctor_get(v_toCold_307_, 2);
lean_inc_ref(v_options_310_);
lean_inc_ref(v_lctx_309_);
v___x_311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_311_, 0, v_env_305_);
lean_ctor_set(v___x_311_, 1, v_mctx_308_);
lean_ctor_set(v___x_311_, 2, v_lctx_309_);
lean_ctor_set(v___x_311_, 3, v_options_310_);
v___x_312_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_msgData_298_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(1);
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2));
v___x_327_ = l_Lean_MessageData_ofFormat(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
return v_x_328_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_353_; 
v_head_330_ = lean_ctor_get(v_x_329_, 0);
v_tail_331_ = lean_ctor_get(v_x_329_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_353_ == 0)
{
v___x_333_ = v_x_329_;
v_isShared_334_ = v_isSharedCheck_353_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_tail_331_);
lean_inc(v_head_330_);
lean_dec(v_x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_353_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_before_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_351_; 
v_before_335_ = lean_ctor_get(v_head_330_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_head_330_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_head_330_, 1);
lean_dec(v_unused_352_);
v___x_337_ = v_head_330_;
v_isShared_338_ = v_isSharedCheck_351_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_before_335_);
lean_dec(v_head_330_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_351_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 7);
lean_ctor_set(v___x_337_, 1, v___x_339_);
lean_ctor_set(v___x_337_, 0, v_x_328_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_x_328_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_350_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 7);
lean_ctor_set(v___x_333_, 1, v___x_342_);
lean_ctor_set(v___x_333_, 0, v___x_341_);
v___x_344_ = v___x_333_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_349_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = l_Lean_MessageData_ofSyntax(v_before_335_);
v___x_346_ = l_Lean_indentD(v___x_345_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_344_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v_x_328_ = v___x_347_;
v_x_329_ = v_tail_331_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object* v_opts_354_, lean_object* v_opt_355_){
_start:
{
lean_object* v_name_356_; lean_object* v_defValue_357_; lean_object* v_map_358_; lean_object* v___x_359_; 
v_name_356_ = lean_ctor_get(v_opt_355_, 0);
v_defValue_357_ = lean_ctor_get(v_opt_355_, 1);
v_map_358_ = lean_ctor_get(v_opts_354_, 0);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_358_, v_name_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
uint8_t v___x_360_; 
v___x_360_ = lean_unbox(v_defValue_357_);
return v___x_360_;
}
else
{
lean_object* v_val_361_; 
v_val_361_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v___x_359_, 1);
if (lean_obj_tag(v_val_361_) == 1)
{
uint8_t v_v_362_; 
v_v_362_ = lean_ctor_get_uint8(v_val_361_, 0);
lean_dec_ref_known(v_val_361_, 0);
return v_v_362_;
}
else
{
uint8_t v___x_363_; 
lean_dec(v_val_361_);
v___x_363_ = lean_unbox(v_defValue_357_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_364_, lean_object* v_opt_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_opts_364_, v_opt_365_);
lean_dec_ref(v_opt_365_);
lean_dec_ref(v_opts_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1));
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object* v_msgData_373_, lean_object* v_macroStack_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_toCold_377_; lean_object* v_options_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_toCold_377_ = lean_ctor_get(v___y_375_, 0);
v_options_378_ = lean_ctor_get(v_toCold_377_, 2);
v___x_379_ = l_Lean_Elab_pp_macroStack;
v___x_380_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_macroStack_374_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_msgData_373_);
return v___x_381_;
}
else
{
if (lean_obj_tag(v_macroStack_374_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_msgData_373_);
return v___x_382_;
}
else
{
lean_object* v_head_383_; lean_object* v_after_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_399_; 
v_head_383_ = lean_ctor_get(v_macroStack_374_, 0);
lean_inc(v_head_383_);
v_after_384_ = lean_ctor_get(v_head_383_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_head_383_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v_head_383_, 0);
lean_dec(v_unused_400_);
v___x_386_ = v_head_383_;
v_isShared_387_ = v_isSharedCheck_399_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_after_384_);
lean_dec(v_head_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_399_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 7);
lean_ctor_set(v___x_386_, 1, v___x_388_);
lean_ctor_set(v___x_386_, 0, v_msgData_373_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_msgData_373_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_398_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_msgData_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_391_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_MessageData_ofSyntax(v_after_384_);
v___x_394_ = l_Lean_indentD(v___x_393_);
v_msgData_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_395_, 0, v___x_392_);
lean_ctor_set(v_msgData_395_, 1, v___x_394_);
v___x_396_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(v_msgData_395_, v_macroStack_374_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_401_, lean_object* v_macroStack_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_401_, v_macroStack_402_, v___y_403_);
lean_dec_ref(v___y_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_ref_414_; lean_object* v___x_415_; lean_object* v_a_416_; lean_object* v_macroStack_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_ref_414_ = lean_ctor_get(v___y_411_, 2);
v___x_415_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_406_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v_macroStack_417_ = lean_ctor_get(v___y_407_, 1);
v___x_418_ = l_Lean_Elab_getBetterRef(v_ref_414_, v_macroStack_417_);
lean_inc(v_macroStack_417_);
v___x_419_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_416_, v_macroStack_417_, v___y_411_);
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_418_);
lean_ctor_set(v___x_424_, 1, v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_437_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Array_mkArray0(lean_box(0));
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_485_ = l_String_toRawSubstring_x27(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_532_, lean_object* v_decl_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
if (lean_obj_tag(v_letOrReassign_532_) == 2)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_533_);
v___x_542_ = l_Lean_Syntax_isOfKind(v_decl_533_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_543_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_544_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_545_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Lean_Syntax_getArg(v_decl_533_, v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_548_);
v___x_550_ = l_Lean_Syntax_isOfKind(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___y_553_; lean_object* v_pattern_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___x_624_; 
v___x_551_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_548_);
v___x_624_ = l_Lean_Syntax_isOfKind(v___x_548_, v___x_551_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_548_);
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_626_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_627_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = l_Lean_Syntax_getArg(v___x_548_, v___x_629_);
v___x_631_ = l_Lean_Syntax_matchesNull(v___x_630_, v___x_547_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_548_);
v___x_632_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_633_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_634_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_635_;
}
else
{
lean_object* v_pattern_636_; lean_object* v_xType_x3f_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_pattern_636_ = l_Lean_Syntax_getArg(v___x_548_, v___x_547_);
v___x_672_ = lean_unsigned_to_nat(2u);
v___x_673_ = l_Lean_Syntax_getArg(v___x_548_, v___x_672_);
v___x_674_ = l_Lean_Syntax_isNone(v___x_673_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
lean_inc(v___x_673_);
v___x_675_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_629_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v___x_673_);
lean_dec(v_pattern_636_);
lean_dec(v___x_548_);
v___x_676_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_677_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_678_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = l_Lean_Syntax_getArg(v___x_673_, v___x_547_);
lean_dec(v___x_673_);
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v___x_680_);
lean_dec(v_pattern_636_);
lean_dec(v___x_548_);
v___x_683_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_684_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_685_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_686_;
}
else
{
lean_object* v_xType_x3f_687_; lean_object* v___x_688_; 
lean_dec(v_decl_533_);
v_xType_x3f_687_ = l_Lean_Syntax_getArg(v___x_680_, v___x_629_);
lean_dec(v___x_680_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_xType_x3f_687_);
v_xType_x3f_638_ = v___x_688_;
v___y_639_ = v_a_534_;
v___y_640_ = v_a_535_;
v___y_641_ = v_a_536_;
v___y_642_ = v_a_537_;
v___y_643_ = v_a_538_;
v___y_644_ = v_a_539_;
goto v___jp_637_;
}
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v___x_673_);
lean_dec(v_decl_533_);
v___x_689_ = lean_box(0);
v_xType_x3f_638_ = v___x_689_;
v___y_639_ = v_a_534_;
v___y_640_ = v_a_535_;
v___y_641_ = v_a_536_;
v___y_642_ = v_a_537_;
v___y_643_ = v_a_538_;
v___y_644_ = v_a_539_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(4u);
v___x_646_ = l_Lean_Syntax_getArg(v___x_548_, v___x_645_);
lean_dec(v___x_548_);
if (lean_obj_tag(v_xType_x3f_638_) == 0)
{
v___y_553_ = v___x_646_;
v_pattern_554_ = v_pattern_636_;
v___y_555_ = v___y_639_;
v___y_556_ = v___y_640_;
v___y_557_ = v___y_641_;
v___y_558_ = v___y_642_;
v___y_559_ = v___y_643_;
v___y_560_ = v___y_644_;
goto v___jp_552_;
}
else
{
lean_object* v_toCold_647_; lean_object* v_val_648_; lean_object* v_ref_649_; lean_object* v_quotContext_650_; lean_object* v_currMacroScope_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_toCold_647_ = lean_ctor_get(v___y_643_, 0);
v_val_648_ = lean_ctor_get(v_xType_x3f_638_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v_xType_x3f_638_, 1);
v_ref_649_ = lean_ctor_get(v___y_643_, 2);
v_quotContext_650_ = lean_ctor_get(v_toCold_647_, 8);
v_currMacroScope_651_ = lean_ctor_get(v_toCold_647_, 9);
v___x_652_ = l_Lean_SourceInfo_fromRef(v_ref_649_, v___x_550_);
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_652_, 7);
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_658_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_659_ = lean_box(0);
lean_inc(v_currMacroScope_651_);
lean_inc(v_quotContext_650_);
v___x_660_ = l_Lean_addMacroScope(v_quotContext_650_, v___x_659_, v_currMacroScope_651_);
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_662_, 0, v___x_652_);
lean_ctor_set(v___x_662_, 1, v___x_658_);
lean_ctor_set(v___x_662_, 2, v___x_660_);
lean_ctor_set(v___x_662_, 3, v___x_661_);
v___x_663_ = l_Lean_Syntax_node1(v___x_652_, v___x_657_, v___x_662_);
v___x_664_ = l_Lean_Syntax_node2(v___x_652_, v___x_654_, v___x_656_, v___x_663_);
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_652_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_668_ = l_Lean_Syntax_node1(v___x_652_, v___x_667_, v_val_648_);
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_652_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_Syntax_node5(v___x_652_, v___x_653_, v___x_664_, v_pattern_636_, v___x_666_, v___x_668_, v___x_670_);
v___y_553_ = v___x_646_;
v_pattern_554_ = v___x_671_;
v___y_555_ = v___y_639_;
v___y_556_ = v___y_640_;
v___y_557_ = v___y_641_;
v___y_558_ = v___y_642_;
v___y_559_ = v___y_643_;
v___y_560_ = v___y_644_;
goto v___jp_552_;
}
}
}
}
v___jp_552_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_561_ = lean_box(0);
v___x_562_ = lean_box(v___x_542_);
v___x_563_ = lean_box(v___x_542_);
lean_inc(v_pattern_554_);
v___x_564_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_564_, 0, v_pattern_554_);
lean_closure_set(v___x_564_, 1, v___x_561_);
lean_closure_set(v___x_564_, 2, v___x_562_);
lean_closure_set(v___x_564_, 3, v___x_563_);
v___x_565_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_564_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
v___x_567_ = lean_infer_type(v_a_566_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = l_Lean_Elab_Term_exprToSyntax(v_a_568_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_toCold_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_607_; 
v_toCold_570_ = lean_ctor_get(v___y_559_, 0);
v_a_571_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_607_ == 0)
{
v___x_573_ = v___x_569_;
v_isShared_574_ = v_isSharedCheck_607_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_607_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_ref_575_; lean_object* v_quotContext_576_; lean_object* v_currMacroScope_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_ref_575_ = lean_ctor_get(v___y_559_, 2);
v_quotContext_576_ = lean_ctor_get(v_toCold_570_, 8);
v_currMacroScope_577_ = lean_ctor_get(v_toCold_570_, 9);
v___x_578_ = l_Lean_SourceInfo_fromRef(v_ref_575_, v___x_550_);
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_580_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_578_, 11);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_578_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_578_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_585_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_578_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_590_ = lean_box(0);
lean_inc(v_currMacroScope_577_);
lean_inc(v_quotContext_576_);
v___x_591_ = l_Lean_addMacroScope(v_quotContext_576_, v___x_590_, v_currMacroScope_577_);
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_593_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_593_, 0, v___x_578_);
lean_ctor_set(v___x_593_, 1, v___x_589_);
lean_ctor_set(v___x_593_, 2, v___x_591_);
lean_ctor_set(v___x_593_, 3, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_578_, v___x_588_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node2(v___x_578_, v___x_585_, v___x_587_, v___x_594_);
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_578_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Syntax_node1(v___x_578_, v___x_579_, v_a_571_);
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_578_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_Syntax_node5(v___x_578_, v___x_584_, v___x_595_, v___y_553_, v___x_597_, v___x_598_, v___x_600_);
lean_inc_ref(v___x_581_);
v___x_602_ = l_Lean_Syntax_node5(v___x_578_, v___x_551_, v_pattern_554_, v___x_581_, v___x_581_, v___x_583_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___x_578_, v___x_541_, v___x_602_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_603_);
v___x_605_ = v___x_573_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v_pattern_554_);
lean_dec(v___y_553_);
return v___x_569_;
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_pattern_554_);
lean_dec(v___y_553_);
v_a_608_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_567_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_567_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_pattern_554_);
lean_dec(v___y_553_);
v_a_616_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_565_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_565_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_Syntax_getArg(v___x_548_, v___x_547_);
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_690_);
v___x_692_ = l_Lean_Syntax_isOfKind(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v___x_690_);
lean_dec(v___x_548_);
v___x_693_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_694_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_695_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_696_;
}
else
{
lean_object* v_x_697_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v_a_706_; lean_object* v_xType_x3f_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_x_697_ = l_Lean_Syntax_getArg(v___x_690_, v___x_547_);
lean_dec(v___x_690_);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_697_);
v___x_784_ = l_Lean_Syntax_isOfKind(v_x_697_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec(v_x_697_);
lean_dec(v___x_548_);
v___x_785_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_786_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_787_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = l_Lean_Syntax_getArg(v___x_548_, v___x_789_);
v___x_791_ = l_Lean_Syntax_matchesNull(v___x_790_, v___x_547_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_x_697_);
lean_dec(v___x_548_);
v___x_792_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_793_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_794_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_unsigned_to_nat(2u);
v___x_797_ = l_Lean_Syntax_getArg(v___x_548_, v___x_796_);
v___x_798_ = l_Lean_Syntax_isNone(v___x_797_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; 
lean_inc(v___x_797_);
v___x_799_ = l_Lean_Syntax_matchesNull(v___x_797_, v___x_789_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v___x_797_);
lean_dec(v_x_697_);
lean_dec(v___x_548_);
v___x_800_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_801_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_802_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = l_Lean_Syntax_getArg(v___x_797_, v___x_547_);
lean_dec(v___x_797_);
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_804_);
v___x_806_ = l_Lean_Syntax_isOfKind(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v___x_804_);
lean_dec(v_x_697_);
lean_dec(v___x_548_);
v___x_807_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_808_ = l_Lean_MessageData_ofSyntax(v_decl_533_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_809_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_810_;
}
else
{
lean_object* v_xType_x3f_811_; lean_object* v___x_812_; 
lean_dec(v_decl_533_);
v_xType_x3f_811_ = l_Lean_Syntax_getArg(v___x_804_, v___x_789_);
lean_dec(v___x_804_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_xType_x3f_811_);
v_xType_x3f_755_ = v___x_812_;
v___y_756_ = v_a_534_;
v___y_757_ = v_a_535_;
v___y_758_ = v_a_536_;
v___y_759_ = v_a_537_;
v___y_760_ = v_a_538_;
v___y_761_ = v_a_539_;
goto v___jp_754_;
}
}
}
else
{
lean_object* v___x_813_; 
lean_dec(v___x_797_);
lean_dec(v_decl_533_);
v___x_813_ = lean_box(0);
v_xType_x3f_755_ = v___x_813_;
v___y_756_ = v_a_534_;
v___y_757_ = v_a_535_;
v___y_758_ = v_a_536_;
v___y_759_ = v_a_537_;
v___y_760_ = v_a_538_;
v___y_761_ = v_a_539_;
goto v___jp_754_;
}
}
}
v___jp_698_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
lean_inc(v_x_697_);
v___x_708_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_697_, v_a_706_, v___x_542_, v___x_542_, v___x_707_, v___y_702_, v___y_704_, v___y_701_, v___y_700_, v___y_699_, v___y_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v___x_708_, 1);
v___x_709_ = l_Lean_TSyntax_getId(v_x_697_);
v___x_710_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_709_, v___y_701_, v___y_700_, v___y_699_, v___y_705_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = l_Lean_LocalDecl_type(v_a_711_);
lean_dec(v_a_711_);
v___x_713_ = l_Lean_Elab_Term_exprToSyntax(v___x_712_, v___y_702_, v___y_704_, v___y_701_, v___y_700_, v___y_699_, v___y_705_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_737_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_737_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_ref_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v_ref_718_ = lean_ctor_get(v___y_699_, 2);
v___x_719_ = 0;
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_718_, v___x_719_);
lean_inc_n(v___x_720_, 7);
v___x_721_ = l_Lean_Syntax_node1(v___x_720_, v___x_691_, v_x_697_);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_723_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_724_, 0, v___x_720_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_720_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_Syntax_node2(v___x_720_, v___x_725_, v___x_727_, v_a_714_);
v___x_729_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_728_);
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_720_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_Syntax_node5(v___x_720_, v___x_549_, v___x_721_, v___x_724_, v___x_729_, v___x_731_, v___y_703_);
v___x_733_ = l_Lean_Syntax_node1(v___x_720_, v___x_541_, v___x_732_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_733_);
v___x_735_ = v___x_716_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_dec(v___y_703_);
lean_dec(v_x_697_);
return v___x_713_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___y_703_);
lean_dec(v_x_697_);
v_a_738_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_710_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_710_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v___y_703_);
lean_dec(v_x_697_);
v_a_746_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_708_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_708_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
v___jp_754_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(4u);
v___x_763_ = l_Lean_Syntax_getArg(v___x_548_, v___x_762_);
lean_dec(v___x_548_);
if (lean_obj_tag(v_xType_x3f_755_) == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_box(0);
v___y_699_ = v___y_760_;
v___y_700_ = v___y_759_;
v___y_701_ = v___y_758_;
v___y_702_ = v___y_756_;
v___y_703_ = v___x_763_;
v___y_704_ = v___y_757_;
v___y_705_ = v___y_761_;
v_a_706_ = v___x_764_;
goto v___jp_698_;
}
else
{
lean_object* v_val_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_782_; 
v_val_765_ = lean_ctor_get(v_xType_x3f_755_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_xType_x3f_755_);
if (v_isSharedCheck_782_ == 0)
{
v___x_767_ = v_xType_x3f_755_;
v_isShared_768_ = v_isSharedCheck_782_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_val_765_);
lean_dec(v_xType_x3f_755_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_782_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Elab_Term_elabType(v_val_765_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_a_770_);
v___x_772_ = v___x_767_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v___y_699_ = v___y_760_;
v___y_700_ = v___y_759_;
v___y_701_ = v___y_758_;
v___y_702_ = v___y_756_;
v___y_703_ = v___x_763_;
v___y_704_ = v___y_757_;
v___y_705_ = v___y_761_;
v_a_706_ = v___x_772_;
goto v___jp_698_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_del_object(v___x_767_);
lean_dec(v___x_763_);
lean_dec(v_x_697_);
v_a_774_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_769_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
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
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v_decl_533_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_815_, lean_object* v_decl_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_815_, v_decl_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_letOrReassign_815_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_835_, lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_835_, v_msg_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_845_, lean_object* v_macroStack_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_845_, v_macroStack_846_, v___y_851_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_855_, lean_object* v_macroStack_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_855_, v_macroStack_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_ref_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_ref_871_ = lean_ctor_get(v___y_868_, 2);
v___x_872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc(v_ref_871_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_ref_871_);
lean_ctor_set(v___x_877_, 1, v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
uint8_t v_postponeValue_904_; uint8_t v_generalize_905_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; 
v_postponeValue_904_ = lean_ctor_get_uint8(v_config_895_, sizeof(void*)*1 + 3);
v_generalize_905_ = lean_ctor_get_uint8(v_config_895_, sizeof(void*)*1 + 4);
if (v_postponeValue_904_ == 0)
{
v___y_907_ = v_a_896_;
v___y_908_ = v_a_897_;
v___y_909_ = v_a_898_;
v___y_910_ = v_a_899_;
v___y_911_ = v_a_900_;
v___y_912_ = v_a_901_;
v___y_913_ = v_a_902_;
goto v___jp_906_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_919_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_918_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_919_;
}
v___jp_906_:
{
if (v_generalize_905_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_917_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_916_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec_ref(v_config_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_930_, lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_931_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_941_, lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_941_, v_msg_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_keyedConfig_989_; uint8_t v_trackZetaDelta_990_; lean_object* v_zetaDeltaSet_991_; lean_object* v_localInstances_992_; lean_object* v_defEqCtx_x3f_993_; lean_object* v_synthPendingDepth_994_; lean_object* v_customCanUnfoldPredicate_x3f_995_; uint8_t v_univApprox_996_; uint8_t v_inTypeClassResolution_997_; uint8_t v_cacheInferType_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_keyedConfig_989_ = lean_ctor_get(v___y_984_, 0);
v_trackZetaDelta_990_ = lean_ctor_get_uint8(v___y_984_, sizeof(void*)*7);
v_zetaDeltaSet_991_ = lean_ctor_get(v___y_984_, 1);
v_localInstances_992_ = lean_ctor_get(v___y_984_, 3);
v_defEqCtx_x3f_993_ = lean_ctor_get(v___y_984_, 4);
v_synthPendingDepth_994_ = lean_ctor_get(v___y_984_, 5);
v_customCanUnfoldPredicate_x3f_995_ = lean_ctor_get(v___y_984_, 6);
v_univApprox_996_ = lean_ctor_get_uint8(v___y_984_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_997_ = lean_ctor_get_uint8(v___y_984_, sizeof(void*)*7 + 2);
v_cacheInferType_998_ = lean_ctor_get_uint8(v___y_984_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_995_);
lean_inc(v_synthPendingDepth_994_);
lean_inc(v_defEqCtx_x3f_993_);
lean_inc_ref(v_localInstances_992_);
lean_inc(v_zetaDeltaSet_991_);
lean_inc_ref(v_keyedConfig_989_);
v___x_999_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_999_, 0, v_keyedConfig_989_);
lean_ctor_set(v___x_999_, 1, v_zetaDeltaSet_991_);
lean_ctor_set(v___x_999_, 2, v_lctx_980_);
lean_ctor_set(v___x_999_, 3, v_localInstances_992_);
lean_ctor_set(v___x_999_, 4, v_defEqCtx_x3f_993_);
lean_ctor_set(v___x_999_, 5, v_synthPendingDepth_994_);
lean_ctor_set(v___x_999_, 6, v_customCanUnfoldPredicate_x3f_995_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*7, v_trackZetaDelta_990_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*7 + 1, v_univApprox_996_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*7 + 2, v_inTypeClassResolution_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*7 + 3, v_cacheInferType_998_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
v___x_1000_ = lean_apply_7(v_x_981_, v___y_982_, v___y_983_, v___x_999_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1019_, lean_object* v_lctx_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1020_, v_x_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_lctx_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1030_, v_lctx_1031_, v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc_ref(v___y_1042_);
v___x_1051_ = lean_apply_9(v_k_1041_, v_b_1045_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, lean_box(0));
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v_b_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1063_, lean_object* v_type_1064_, lean_object* v_val_1065_, lean_object* v_k_1066_, uint8_t v_nondep_1067_, uint8_t v_kind_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; 
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc_ref(v___y_1069_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1077_, 0, v_k_1066_);
lean_closure_set(v___f_1077_, 1, v___y_1069_);
lean_closure_set(v___f_1077_, 2, v___y_1070_);
lean_closure_set(v___f_1077_, 3, v___y_1071_);
v___x_1078_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1063_, v_type_1064_, v_val_1065_, v___f_1077_, v_nondep_1067_, v_kind_1068_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1078_) == 0)
{
return v___x_1078_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1087_, lean_object* v_type_1088_, lean_object* v_val_1089_, lean_object* v_k_1090_, lean_object* v_nondep_1091_, lean_object* v_kind_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v_nondep_boxed_1101_; uint8_t v_kind_boxed_1102_; lean_object* v_res_1103_; 
v_nondep_boxed_1101_ = lean_unbox(v_nondep_1091_);
v_kind_boxed_1102_ = lean_unbox(v_kind_1092_);
v_res_1103_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1087_, v_type_1088_, v_val_1089_, v_k_1090_, v_nondep_boxed_1101_, v_kind_boxed_1102_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1104_, lean_object* v_name_1105_, lean_object* v_type_1106_, lean_object* v_val_1107_, lean_object* v_k_1108_, uint8_t v_nondep_1109_, uint8_t v_kind_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1105_, v_type_1106_, v_val_1107_, v_k_1108_, v_nondep_1109_, v_kind_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_name_1121_, lean_object* v_type_1122_, lean_object* v_val_1123_, lean_object* v_k_1124_, lean_object* v_nondep_1125_, lean_object* v_kind_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
uint8_t v_nondep_boxed_1135_; uint8_t v_kind_boxed_1136_; lean_object* v_res_1137_; 
v_nondep_boxed_1135_ = lean_unbox(v_nondep_1125_);
v_kind_boxed_1136_ = lean_unbox(v_kind_1126_);
v_res_1137_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1120_, v_name_1121_, v_type_1122_, v_val_1123_, v_k_1124_, v_nondep_boxed_1135_, v_kind_boxed_1136_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1138_, lean_object* v___x_1139_, uint8_t v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, uint8_t v___x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1138_, v___x_1139_, v___x_1140_, v___x_1140_, v___x_1141_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = 1;
v___x_1154_ = l_Lean_Meta_mkLambdaFVars(v___x_1142_, v_a_1152_, v___x_1143_, v___x_1143_, v___x_1143_, v___x_1140_, v___x_1153_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1154_;
}
else
{
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v___x_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
uint8_t v___x_85759__boxed_1168_; uint8_t v___x_85762__boxed_1169_; lean_object* v_res_1170_; 
v___x_85759__boxed_1168_ = lean_unbox(v___x_1157_);
v___x_85762__boxed_1169_ = lean_unbox(v___x_1160_);
v_res_1170_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1155_, v___x_1156_, v___x_85759__boxed_1168_, v___x_1158_, v___x_1159_, v___x_85762__boxed_1169_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v___x_1159_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v_ks_1175_; lean_object* v_vs_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_ks_1175_ = lean_ctor_get(v_x_1171_, 0);
v_vs_1176_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v_x_1171_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_vs_1176_);
lean_inc(v_ks_1175_);
lean_dec(v_x_1171_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_ks_1175_);
v___x_1181_ = lean_nat_dec_lt(v_x_1172_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_x_1172_);
v___x_1182_ = lean_array_push(v_ks_1175_, v_x_1173_);
v___x_1183_ = lean_array_push(v_vs_1176_, v_x_1174_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1183_);
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_object* v_k_x27_1187_; uint8_t v___x_1188_; 
v_k_x27_1187_ = lean_array_fget_borrowed(v_ks_1175_, v_x_1172_);
v___x_1188_ = l_Lean_instBEqFVarId_beq(v_x_1173_, v_k_x27_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
if (v_isShared_1179_ == 0)
{
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ks_1175_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_vs_1176_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_x_1172_, v___x_1191_);
lean_dec(v_x_1172_);
v_x_1171_ = v___x_1190_;
v_x_1172_ = v___x_1192_;
goto _start;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_array_fset(v_ks_1175_, v_x_1172_, v_x_1173_);
v___x_1196_ = lean_array_fset(v_vs_1176_, v_x_1172_, v_x_1174_);
lean_dec(v_x_1172_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1196_);
lean_ctor_set(v___x_1178_, 0, v___x_1195_);
v___x_1198_ = v___x_1178_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1201_, lean_object* v_k_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1201_, v___x_1204_, v_k_1202_, v_v_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1207_, size_t v_x_1208_, size_t v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
if (lean_obj_tag(v_x_1207_) == 0)
{
lean_object* v_es_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v_j_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_es_1212_ = lean_ctor_get(v_x_1207_, 0);
v___x_1213_ = ((size_t)31ULL);
v___x_1214_ = lean_usize_land(v_x_1208_, v___x_1213_);
v_j_1215_ = lean_usize_to_nat(v___x_1214_);
v___x_1216_ = lean_array_get_size(v_es_1212_);
v___x_1217_ = lean_nat_dec_lt(v_j_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_j_1215_);
lean_dec(v_x_1211_);
lean_dec(v_x_1210_);
return v_x_1207_;
}
else
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1256_; 
lean_inc_ref(v_es_1212_);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_x_1207_, 0);
lean_dec(v_unused_1257_);
v___x_1219_ = v_x_1207_;
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_x_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1256_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_v_1221_; lean_object* v___x_1222_; lean_object* v_xs_x27_1223_; lean_object* v___y_1225_; 
v_v_1221_ = lean_array_fget(v_es_1212_, v_j_1215_);
v___x_1222_ = lean_box(0);
v_xs_x27_1223_ = lean_array_fset(v_es_1212_, v_j_1215_, v___x_1222_);
switch(lean_obj_tag(v_v_1221_))
{
case 0:
{
lean_object* v_key_1230_; lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
v_key_1230_ = lean_ctor_get(v_v_1221_, 0);
v_val_1231_ = lean_ctor_get(v_v_1221_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v_v_1221_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_inc(v_key_1230_);
lean_dec(v_v_1221_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Lean_instBEqFVarId_beq(v_x_1210_, v_key_1230_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_del_object(v___x_1233_);
v___x_1236_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1230_, v_val_1231_, v_x_1210_, v_x_1211_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
v___y_1225_ = v___x_1237_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_val_1231_);
lean_dec(v_key_1230_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v_x_1211_);
lean_ctor_set(v___x_1233_, 0, v_x_1210_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_x_1210_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_x_1211_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v___y_1225_ = v___x_1239_;
goto v___jp_1224_;
}
}
}
}
case 1:
{
lean_object* v_node_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
v_node_1242_ = lean_ctor_get(v_v_1221_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1244_ = v_v_1221_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_node_1242_);
lean_dec(v_v_1221_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_shift_right(v_x_1208_, v___x_1246_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_x_1209_, v___x_1248_);
v___x_1250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1242_, v___x_1247_, v___x_1249_, v_x_1210_, v_x_1211_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1250_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1225_ = v___x_1252_;
goto v___jp_1224_;
}
}
}
default: 
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_x_1210_);
lean_ctor_set(v___x_1255_, 1, v_x_1211_);
v___y_1225_ = v___x_1255_;
goto v___jp_1224_;
}
}
v___jp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_array_fset(v_xs_x27_1223_, v_j_1215_, v___y_1225_);
lean_dec(v_j_1215_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1226_);
v___x_1228_ = v___x_1219_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_ks_1258_; lean_object* v_vs_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1277_; 
v_ks_1258_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1259_ = lean_ctor_get(v_x_1207_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1261_ = v_x_1207_;
v_isShared_1262_ = v_isSharedCheck_1277_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_vs_1259_);
lean_inc(v_ks_1258_);
lean_dec(v_x_1207_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1277_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_ks_1258_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_vs_1259_);
v___x_1264_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v_newNode_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v_newNode_1265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1264_, v_x_1210_, v_x_1211_);
v___x_1266_ = ((size_t)7ULL);
v___x_1267_ = lean_usize_dec_le(v___x_1266_, v_x_1209_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1265_);
v___x_1269_ = lean_unsigned_to_nat(4u);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
if (v___x_1270_ == 0)
{
lean_object* v_ks_1271_; lean_object* v_vs_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_ks_1271_ = lean_ctor_get(v_newNode_1265_, 0);
lean_inc_ref(v_ks_1271_);
v_vs_1272_ = lean_ctor_get(v_newNode_1265_, 1);
lean_inc_ref(v_vs_1272_);
lean_dec_ref(v_newNode_1265_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1209_, v_ks_1271_, v_vs_1272_, v___x_1273_, v___x_1274_);
lean_dec_ref(v_vs_1272_);
lean_dec_ref(v_ks_1271_);
return v___x_1275_;
}
else
{
return v_newNode_1265_;
}
}
else
{
return v_newNode_1265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_i_1281_, lean_object* v_entries_1282_){
_start:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_array_get_size(v_keys_1279_);
v___x_1284_ = lean_nat_dec_lt(v_i_1281_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_dec(v_i_1281_);
return v_entries_1282_;
}
else
{
lean_object* v_k_1285_; lean_object* v_v_1286_; uint64_t v___x_1287_; size_t v_h_1288_; size_t v___x_1289_; lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v_h_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_k_1285_ = lean_array_fget_borrowed(v_keys_1279_, v_i_1281_);
v_v_1286_ = lean_array_fget_borrowed(v_vals_1280_, v_i_1281_);
v___x_1287_ = l_Lean_instHashableFVarId_hash(v_k_1285_);
v_h_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = ((size_t)5ULL);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_sub(v_depth_1278_, v___x_1291_);
v___x_1293_ = lean_usize_mul(v___x_1289_, v___x_1292_);
v_h_1294_ = lean_usize_shift_right(v_h_1288_, v___x_1293_);
v___x_1295_ = lean_nat_add(v_i_1281_, v___x_1290_);
lean_dec(v_i_1281_);
lean_inc(v_v_1286_);
lean_inc(v_k_1285_);
v___x_1296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1282_, v_h_1294_, v_depth_1278_, v_k_1285_, v_v_1286_);
v_i_1281_ = v___x_1295_;
v_entries_1282_ = v___x_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1298_, lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_entries_1302_){
_start:
{
size_t v_depth_boxed_1303_; lean_object* v_res_1304_; 
v_depth_boxed_1303_ = lean_unbox_usize(v_depth_1298_);
lean_dec(v_depth_1298_);
v_res_1304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1303_, v_keys_1299_, v_vals_1300_, v_i_1301_, v_entries_1302_);
lean_dec_ref(v_vals_1300_);
lean_dec_ref(v_keys_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
size_t v_x_85882__boxed_1310_; size_t v_x_85883__boxed_1311_; lean_object* v_res_1312_; 
v_x_85882__boxed_1310_ = lean_unbox_usize(v_x_1306_);
lean_dec(v_x_1306_);
v_x_85883__boxed_1311_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_res_1312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1305_, v_x_85882__boxed_1310_, v_x_85883__boxed_1311_, v_x_1308_, v_x_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = l_Lean_instHashableFVarId_hash(v_x_1314_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1313_, v___x_1317_, v___x_1318_, v_x_1314_, v_x_1315_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1320_, size_t v_i_1321_, size_t v_stop_1322_, lean_object* v_b_1323_){
_start:
{
lean_object* v___y_1325_; uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_eq(v_i_1321_, v_stop_1322_);
if (v___x_1329_ == 0)
{
lean_object* v_fvarIdToDecl_1330_; lean_object* v_decls_1331_; lean_object* v_auxDeclToFullName_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_fvarIdToDecl_1330_ = lean_ctor_get(v_b_1323_, 0);
v_decls_1331_ = lean_ctor_get(v_b_1323_, 1);
v_auxDeclToFullName_1332_ = lean_ctor_get(v_b_1323_, 2);
v___x_1333_ = lean_array_uget_borrowed(v_as_1320_, v_i_1321_);
v___x_1334_ = l_Lean_Expr_fvarId_x21(v___x_1333_);
lean_inc_ref(v_b_1323_);
v___x_1335_ = lean_local_ctx_find(v_b_1323_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
v___y_1325_ = v_b_1323_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1362_; 
lean_inc(v_auxDeclToFullName_1332_);
lean_inc_ref(v_decls_1331_);
lean_inc_ref(v_fvarIdToDecl_1330_);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_b_1323_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1363_ = lean_ctor_get(v_b_1323_, 2);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_b_1323_, 1);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_b_1323_, 0);
lean_dec(v_unused_1365_);
v___x_1337_ = v_b_1323_;
v_isShared_1338_ = v_isSharedCheck_1362_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v_b_1323_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1362_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_val_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1361_; 
v_val_1339_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1341_ = v___x_1335_;
v_isShared_1342_ = v_isSharedCheck_1361_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_val_1339_);
lean_dec(v___x_1335_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1361_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1357_; lean_object* v_fvarId_1360_; 
v___x_1343_ = l_Lean_LocalDecl_type(v_val_1339_);
v___x_1344_ = l_Lean_Expr_cleanupAnnotations(v___x_1343_);
v___x_1345_ = l_Lean_LocalDecl_setType(v_val_1339_, v___x_1344_);
v_fvarId_1360_ = lean_ctor_get(v___x_1345_, 1);
lean_inc(v_fvarId_1360_);
v___y_1357_ = v_fvarId_1360_;
goto v___jp_1356_;
v___jp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1345_);
v___x_1350_ = v___x_1341_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1345_);
v___x_1350_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = l_Lean_PersistentArray_set___redArg(v_decls_1331_, v___y_1348_, v___x_1350_);
lean_dec(v___y_1348_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___x_1351_);
lean_ctor_set(v___x_1337_, 0, v___y_1347_);
v___x_1353_ = v___x_1337_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___y_1347_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_auxDeclToFullName_1332_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
v___y_1325_ = v___x_1353_;
goto v___jp_1324_;
}
}
}
v___jp_1356_:
{
lean_object* v___x_1358_; lean_object* v_index_1359_; 
lean_inc_ref(v___x_1345_);
v___x_1358_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1330_, v___y_1357_, v___x_1345_);
v_index_1359_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_index_1359_);
v___y_1347_ = v___x_1358_;
v___y_1348_ = v_index_1359_;
goto v___jp_1346_;
}
}
}
}
}
else
{
return v_b_1323_;
}
v___jp_1324_:
{
size_t v___x_1326_; size_t v___x_1327_; 
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1321_, v___x_1326_);
v_i_1321_ = v___x_1327_;
v_b_1323_ = v___y_1325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1366_, lean_object* v_i_1367_, lean_object* v_stop_1368_, lean_object* v_b_1369_){
_start:
{
size_t v_i_boxed_1370_; size_t v_stop_boxed_1371_; lean_object* v_res_1372_; 
v_i_boxed_1370_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_stop_boxed_1371_ = lean_unbox_usize(v_stop_1368_);
lean_dec(v_stop_1368_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1366_, v_i_boxed_1370_, v_stop_boxed_1371_, v_b_1369_);
lean_dec_ref(v_as_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_bs_1375_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1374_, v_sz_1373_);
if (v___x_1376_ == 0)
{
return v_bs_1375_;
}
else
{
lean_object* v_v_1377_; lean_object* v_snd_1378_; lean_object* v___x_1379_; lean_object* v_bs_x27_1380_; size_t v___x_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v_v_1377_ = lean_array_uget_borrowed(v_bs_1375_, v_i_1374_);
v_snd_1378_ = lean_ctor_get(v_v_1377_, 1);
lean_inc(v_snd_1378_);
v___x_1379_ = lean_unsigned_to_nat(0u);
v_bs_x27_1380_ = lean_array_uset(v_bs_1375_, v_i_1374_, v___x_1379_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1374_, v___x_1381_);
v___x_1383_ = lean_array_uset(v_bs_x27_1380_, v_i_1374_, v_snd_1378_);
v_i_1374_ = v___x_1382_;
v_bs_1375_ = v___x_1383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_bs_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1388_, v_i_boxed_1389_, v_bs_1387_);
return v_res_1390_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1393_ = l_Lean_stringToMessageData(v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1399_ = l_Lean_stringToMessageData(v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1402_, lean_object* v_value_1403_, uint8_t v___x_1404_, uint8_t v___x_1405_, lean_object* v___x_1406_, uint8_t v___y_1407_, lean_object* v_xs_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
lean_inc(v_type_1402_);
v___x_1416_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1416_, 0, v_type_1402_);
v___x_1417_ = 2;
v___x_1418_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1416_, v___x_1417_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___y_1424_; lean_object* v___y_1460_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v_sz_1420_ = lean_array_size(v_xs_1408_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1420_, v___x_1421_, v_xs_1408_);
if (v___y_1407_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1460_ = v___x_1496_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1460_ = v___x_1497_;
goto v___jp_1459_;
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; 
lean_inc(v_a_1419_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1419_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_box(v___x_1404_);
v___x_1428_ = lean_box(v___x_1405_);
lean_inc_ref(v___x_1422_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1429_, 0, v_value_1403_);
lean_closure_set(v___f_1429_, 1, v___x_1425_);
lean_closure_set(v___f_1429_, 2, v___x_1427_);
lean_closure_set(v___f_1429_, 3, v___x_1426_);
lean_closure_set(v___f_1429_, 4, v___x_1422_);
lean_closure_set(v___f_1429_, 5, v___x_1428_);
v___x_1430_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1424_, v___f_1429_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = 1;
v___x_1433_ = l_Lean_Meta_mkForallFVars(v___x_1422_, v_a_1419_, v___x_1405_, v___x_1404_, v___x_1404_, v___x_1432_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___x_1422_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_a_1434_);
lean_ctor_set(v___x_1438_, 1, v_a_1431_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1431_);
v_a_1443_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1433_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1433_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
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
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___x_1422_);
lean_dec(v_a_1419_);
v_a_1451_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1430_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1430_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1460_);
v___x_1462_ = l_Lean_stringToMessageData(v___y_1460_);
lean_inc_ref(v___x_1462_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_inc(v_type_1402_);
v___x_1466_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1419_, v_type_1402_, v___x_1465_, v___y_1410_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref_known(v___x_1466_, 1);
v___x_1467_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1462_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___x_1464_);
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_inc(v_a_1419_);
v___x_1471_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1419_, v_type_1402_, v___x_1470_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_lctx_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
lean_dec_ref_known(v___x_1471_, 1);
v_lctx_1472_ = lean_ctor_get(v___y_1411_, 2);
v___x_1473_ = lean_array_get_size(v___x_1422_);
v___x_1474_ = lean_nat_dec_lt(v___x_1406_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_inc_ref(v_lctx_1472_);
v___y_1424_ = v_lctx_1472_;
goto v___jp_1423_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_nat_dec_le(v___x_1473_, v___x_1473_);
if (v___x_1475_ == 0)
{
if (v___x_1474_ == 0)
{
lean_inc_ref(v_lctx_1472_);
v___y_1424_ = v_lctx_1472_;
goto v___jp_1423_;
}
else
{
size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_usize_of_nat(v___x_1473_);
lean_inc_ref(v_lctx_1472_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1422_, v___x_1421_, v___x_1476_, v_lctx_1472_);
v___y_1424_ = v___x_1477_;
goto v___jp_1423_;
}
}
else
{
size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_usize_of_nat(v___x_1473_);
lean_inc_ref(v_lctx_1472_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1422_, v___x_1421_, v___x_1478_, v_lctx_1472_);
v___y_1424_ = v___x_1479_;
goto v___jp_1423_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1422_);
lean_dec(v_a_1419_);
lean_dec(v_value_1403_);
v_a_1480_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1471_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1471_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v___x_1462_);
lean_dec_ref(v___x_1422_);
lean_dec(v_a_1419_);
lean_dec(v_value_1403_);
lean_dec(v_type_1402_);
v_a_1488_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1466_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1466_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_xs_1408_);
lean_dec(v_value_1403_);
lean_dec(v_type_1402_);
v_a_1498_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1418_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1418_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1506_, lean_object* v_value_1507_, lean_object* v___x_1508_, lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v___y_1511_, lean_object* v_xs_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v___x_86191__boxed_1520_; uint8_t v___x_86192__boxed_1521_; uint8_t v___y_86194__boxed_1522_; lean_object* v_res_1523_; 
v___x_86191__boxed_1520_ = lean_unbox(v___x_1508_);
v___x_86192__boxed_1521_ = lean_unbox(v___x_1509_);
v___y_86194__boxed_1522_ = lean_unbox(v___y_1511_);
v_res_1523_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1506_, v_value_1507_, v___x_86191__boxed_1520_, v___x_86192__boxed_1521_, v___x_1510_, v___y_86194__boxed_1522_, v_xs_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___x_1510_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1524_, lean_object* v_a_1525_, uint8_t v_zeta_1526_, uint8_t v___y_1527_, lean_object* v_x_1528_, uint8_t v_usedOnly_1529_, uint8_t v___x_1530_, lean_object* v_snd_1531_, lean_object* v_h_x27_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
lean_inc_ref(v_h_x27_1532_);
v___x_1541_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1524_, v_h_x27_1532_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v___x_1541_, 1);
v___x_1542_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1525_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
if (v_zeta_1526_ == 0)
{
if (v___y_1527_ == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v_snd_1531_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_unsigned_to_nat(2u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1544_);
v___x_1546_ = lean_array_push(v___x_1545_, v_x_1528_);
v___x_1547_ = lean_array_push(v___x_1546_, v_h_x27_1532_);
v___x_1548_ = 1;
v___x_1549_ = l_Lean_Meta_mkLetFVars(v___x_1547_, v_a_1543_, v_usedOnly_1529_, v___y_1527_, v___x_1548_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec_ref(v___x_1547_);
return v___x_1549_;
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1550_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1551_ = lean_unsigned_to_nat(2u);
v___x_1552_ = lean_mk_empty_array_with_capacity(v___x_1551_);
v___x_1553_ = lean_array_push(v___x_1552_, v_x_1528_);
v___x_1554_ = lean_array_push(v___x_1553_, v_h_x27_1532_);
v___x_1555_ = 1;
v___x_1556_ = l_Lean_Meta_mkLambdaFVars(v___x_1554_, v_a_1550_, v_zeta_1526_, v___x_1530_, v_zeta_1526_, v___x_1530_, v___x_1555_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec_ref(v___x_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
lean_inc_ref(v_snd_1531_);
v___x_1558_ = l_Lean_Meta_mkEqRefl(v_snd_1531_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = l_Lean_mkAppB(v_a_1557_, v_snd_1531_, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_dec(v_a_1557_);
lean_dec_ref(v_snd_1531_);
return v___x_1558_;
}
}
else
{
lean_dec_ref(v_snd_1531_);
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1568_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1569_ = lean_unsigned_to_nat(2u);
v___x_1570_ = lean_mk_empty_array_with_capacity(v___x_1569_);
lean_inc_ref(v___x_1570_);
v___x_1571_ = lean_array_push(v___x_1570_, v_x_1528_);
v___x_1572_ = lean_array_push(v___x_1571_, v_h_x27_1532_);
v___x_1573_ = l_Lean_Expr_abstractM(v_a_1568_, v___x_1572_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec_ref(v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
lean_inc_ref(v_snd_1531_);
v___x_1575_ = l_Lean_Meta_mkEqRefl(v_snd_1531_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1586_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1580_ = lean_array_push(v___x_1570_, v_snd_1531_);
v___x_1581_ = lean_array_push(v___x_1580_, v_a_1576_);
v___x_1582_ = lean_expr_instantiate_rev(v_a_1574_, v___x_1581_);
lean_dec_ref(v___x_1581_);
lean_dec(v_a_1574_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1582_);
v___x_1584_ = v___x_1578_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_dec(v_a_1574_);
lean_dec_ref(v___x_1570_);
lean_dec_ref(v_snd_1531_);
return v___x_1575_;
}
}
else
{
lean_dec_ref(v___x_1570_);
lean_dec_ref(v_snd_1531_);
return v___x_1573_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1532_);
lean_dec_ref(v_snd_1531_);
lean_dec_ref(v_x_1528_);
return v___x_1542_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_h_x27_1532_);
lean_dec_ref(v_snd_1531_);
lean_dec_ref(v_x_1528_);
lean_dec_ref(v_a_1525_);
v_a_1587_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1541_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1541_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1595_ = _args[0];
lean_object* v_a_1596_ = _args[1];
lean_object* v_zeta_1597_ = _args[2];
lean_object* v___y_1598_ = _args[3];
lean_object* v_x_1599_ = _args[4];
lean_object* v_usedOnly_1600_ = _args[5];
lean_object* v___x_1601_ = _args[6];
lean_object* v_snd_1602_ = _args[7];
lean_object* v_h_x27_1603_ = _args[8];
lean_object* v___y_1604_ = _args[9];
lean_object* v___y_1605_ = _args[10];
lean_object* v___y_1606_ = _args[11];
lean_object* v___y_1607_ = _args[12];
lean_object* v___y_1608_ = _args[13];
lean_object* v___y_1609_ = _args[14];
lean_object* v___y_1610_ = _args[15];
lean_object* v___y_1611_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1612_; uint8_t v___y_86418__boxed_1613_; uint8_t v_usedOnly_boxed_1614_; uint8_t v___x_86419__boxed_1615_; lean_object* v_res_1616_; 
v_zeta_boxed_1612_ = lean_unbox(v_zeta_1597_);
v___y_86418__boxed_1613_ = lean_unbox(v___y_1598_);
v_usedOnly_boxed_1614_ = lean_unbox(v_usedOnly_1600_);
v___x_86419__boxed_1615_ = lean_unbox(v___x_1601_);
v_res_1616_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1595_, v_a_1596_, v_zeta_boxed_1612_, v___y_86418__boxed_1613_, v_x_1599_, v_usedOnly_boxed_1614_, v___x_86419__boxed_1615_, v_snd_1602_, v_h_x27_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1617_, lean_object* v_a_1618_, uint8_t v_zeta_1619_, lean_object* v_x_1620_, uint8_t v_usedOnly_1621_, lean_object* v_snd_1622_, uint8_t v___y_1623_, uint8_t v___x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1617_) == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1618_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
if (v_zeta_1619_ == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_snd_1622_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_array_push(v___x_1636_, v_x_1620_);
v___x_1638_ = 1;
v___x_1639_ = l_Lean_Meta_mkLetFVars(v___x_1637_, v_a_1634_, v_usedOnly_1621_, v_zeta_1619_, v___x_1638_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec_ref(v___x_1637_);
return v___x_1639_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_mk_empty_array_with_capacity(v___x_1641_);
v___x_1643_ = lean_array_push(v___x_1642_, v_x_1620_);
v___x_1644_ = l_Lean_Expr_abstractM(v_a_1640_, v___x_1643_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec_ref(v___x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1653_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1653_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_expr_instantiate1(v_a_1645_, v_snd_1622_);
lean_dec_ref(v_snd_1622_);
lean_dec(v_a_1645_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1649_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
lean_dec_ref(v_snd_1622_);
return v___x_1644_;
}
}
}
else
{
lean_dec_ref(v_snd_1622_);
lean_dec_ref(v_x_1620_);
return v___x_1633_;
}
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1655_; 
v_val_1654_ = lean_ctor_get(v_eq_x3f_1617_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v_eq_x3f_1617_, 1);
lean_inc_ref(v_snd_1622_);
lean_inc_ref(v_x_1620_);
v___x_1655_ = l_Lean_Meta_mkEq(v_x_1620_, v_snd_1622_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
lean_inc_ref(v_x_1620_);
v___x_1657_ = l_Lean_Meta_mkEqRefl(v_x_1620_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = lean_box(v_zeta_1619_);
v___x_1660_ = lean_box(v___y_1623_);
v___x_1661_ = lean_box(v_usedOnly_1621_);
v___x_1662_ = lean_box(v___x_1624_);
lean_inc(v_val_1654_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 17, 8);
lean_closure_set(v___f_1663_, 0, v_val_1654_);
lean_closure_set(v___f_1663_, 1, v_a_1618_);
lean_closure_set(v___f_1663_, 2, v___x_1659_);
lean_closure_set(v___f_1663_, 3, v___x_1660_);
lean_closure_set(v___f_1663_, 4, v_x_1620_);
lean_closure_set(v___f_1663_, 5, v___x_1661_);
lean_closure_set(v___f_1663_, 6, v___x_1662_);
lean_closure_set(v___f_1663_, 7, v_snd_1622_);
v___x_1664_ = l_Lean_TSyntax_getId(v_val_1654_);
lean_dec(v_val_1654_);
v___x_1665_ = 0;
v___x_1666_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1664_, v_a_1656_, v_a_1658_, v___f_1663_, v___x_1624_, v___x_1665_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1666_;
}
else
{
lean_dec(v_a_1656_);
lean_dec(v_val_1654_);
lean_dec_ref(v_snd_1622_);
lean_dec_ref(v_x_1620_);
lean_dec_ref(v_a_1618_);
return v___x_1657_;
}
}
else
{
lean_dec(v_val_1654_);
lean_dec_ref(v_snd_1622_);
lean_dec_ref(v_x_1620_);
lean_dec_ref(v_a_1618_);
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object* v_eq_x3f_1667_, lean_object* v_a_1668_, lean_object* v_zeta_1669_, lean_object* v_x_1670_, lean_object* v_usedOnly_1671_, lean_object* v_snd_1672_, lean_object* v___y_1673_, lean_object* v___x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_zeta_boxed_1683_; uint8_t v_usedOnly_boxed_1684_; uint8_t v___y_86571__boxed_1685_; uint8_t v___x_86572__boxed_1686_; lean_object* v_res_1687_; 
v_zeta_boxed_1683_ = lean_unbox(v_zeta_1669_);
v_usedOnly_boxed_1684_ = lean_unbox(v_usedOnly_1671_);
v___y_86571__boxed_1685_ = lean_unbox(v___y_1673_);
v___x_86572__boxed_1686_ = lean_unbox(v___x_1674_);
v_res_1687_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1667_, v_a_1668_, v_zeta_boxed_1683_, v_x_1670_, v_usedOnly_boxed_1684_, v_snd_1672_, v___y_86571__boxed_1685_, v___x_86572__boxed_1686_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1688_, lean_object* v_eq_x3f_1689_, lean_object* v_a_1690_, uint8_t v_zeta_1691_, uint8_t v_usedOnly_1692_, lean_object* v_snd_1693_, uint8_t v___y_1694_, uint8_t v___x_1695_, lean_object* v_letOrReassign_1696_, lean_object* v_a_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
lean_inc_ref(v_x_1698_);
v___x_1707_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1688_, v_x_1698_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___y_1712_; lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1707_, 1);
v___x_1708_ = lean_box(v_zeta_1691_);
v___x_1709_ = lean_box(v_usedOnly_1692_);
v___x_1710_ = lean_box(v___y_1694_);
v___x_1711_ = lean_box(v___x_1695_);
v___y_1712_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 16, 8);
lean_closure_set(v___y_1712_, 0, v_eq_x3f_1689_);
lean_closure_set(v___y_1712_, 1, v_a_1690_);
lean_closure_set(v___y_1712_, 2, v___x_1708_);
lean_closure_set(v___y_1712_, 3, v_x_1698_);
lean_closure_set(v___y_1712_, 4, v___x_1709_);
lean_closure_set(v___y_1712_, 5, v_snd_1693_);
lean_closure_set(v___y_1712_, 6, v___x_1710_);
lean_closure_set(v___y_1712_, 7, v___x_1711_);
v___x_1713_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1696_, v_a_1697_, v___y_1712_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1713_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v_x_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_letOrReassign_1696_);
lean_dec_ref(v_snd_1693_);
lean_dec_ref(v_a_1690_);
lean_dec(v_eq_x3f_1689_);
v_a_1714_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1707_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1707_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1722_ = _args[0];
lean_object* v_eq_x3f_1723_ = _args[1];
lean_object* v_a_1724_ = _args[2];
lean_object* v_zeta_1725_ = _args[3];
lean_object* v_usedOnly_1726_ = _args[4];
lean_object* v_snd_1727_ = _args[5];
lean_object* v___y_1728_ = _args[6];
lean_object* v___x_1729_ = _args[7];
lean_object* v_letOrReassign_1730_ = _args[8];
lean_object* v_a_1731_ = _args[9];
lean_object* v_x_1732_ = _args[10];
lean_object* v___y_1733_ = _args[11];
lean_object* v___y_1734_ = _args[12];
lean_object* v___y_1735_ = _args[13];
lean_object* v___y_1736_ = _args[14];
lean_object* v___y_1737_ = _args[15];
lean_object* v___y_1738_ = _args[16];
lean_object* v___y_1739_ = _args[17];
lean_object* v___y_1740_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_1741_; uint8_t v_usedOnly_boxed_1742_; uint8_t v___y_86679__boxed_1743_; uint8_t v___x_86680__boxed_1744_; lean_object* v_res_1745_; 
v_zeta_boxed_1741_ = lean_unbox(v_zeta_1725_);
v_usedOnly_boxed_1742_ = lean_unbox(v_usedOnly_1726_);
v___y_86679__boxed_1743_ = lean_unbox(v___y_1728_);
v___x_86680__boxed_1744_ = lean_unbox(v___x_1729_);
v_res_1745_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1722_, v_eq_x3f_1723_, v_a_1724_, v_zeta_boxed_1741_, v_usedOnly_boxed_1742_, v_snd_1727_, v___y_86679__boxed_1743_, v___x_86680__boxed_1744_, v_letOrReassign_1730_, v_a_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1746_, lean_object* v_____do__lift_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1747_, v___x_1746_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1758_, lean_object* v_____do__lift_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_86747__boxed_1768_; lean_object* v_res_1769_; 
v___x_86747__boxed_1768_ = lean_unbox(v___x_1758_);
v_res_1769_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_86747__boxed_1768_, v_____do__lift_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v_____do__lift_1759_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1770_, lean_object* v___x_1771_, uint8_t v___x_1772_, lean_object* v___x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1770_, v___x_1771_, v___x_1772_, v___x_1772_, v___x_1773_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v___x_86782__boxed_1795_; lean_object* v_res_1796_; 
v___x_86782__boxed_1795_ = lean_unbox(v___x_1785_);
v_res_1796_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1783_, v___x_1784_, v___x_86782__boxed_1795_, v___x_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
lean_inc_ref(v___y_1798_);
v___x_1806_ = lean_apply_8(v_x_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, lean_box(0));
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec_ref(v___y_1808_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1817_, lean_object* v_mkInfoTree_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v_a_1824_, lean_object* v_a_x3f_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_infoState_1828_; lean_object* v_trees_1829_; lean_object* v___x_1830_; 
v___x_1827_ = lean_st_ref_get(v___y_1817_);
v_infoState_1828_ = lean_ctor_get(v___x_1827_, 7);
lean_inc_ref(v_infoState_1828_);
lean_dec(v___x_1827_);
v_trees_1829_ = lean_ctor_get(v_infoState_1828_, 2);
lean_inc_ref(v_trees_1829_);
lean_dec_ref(v_infoState_1828_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1823_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
v___x_1830_ = lean_apply_8(v_mkInfoTree_1818_, v_trees_1829_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1817_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1869_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1869_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1869_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v_infoState_1836_; lean_object* v_env_1837_; lean_object* v_nextMacroScope_1838_; lean_object* v_ngen_1839_; lean_object* v_auxDeclNGen_1840_; lean_object* v_traceState_1841_; lean_object* v_cache_1842_; lean_object* v_messages_1843_; lean_object* v_snapshotTasks_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1868_; 
v___x_1835_ = lean_st_ref_take(v___y_1817_);
v_infoState_1836_ = lean_ctor_get(v___x_1835_, 7);
v_env_1837_ = lean_ctor_get(v___x_1835_, 0);
v_nextMacroScope_1838_ = lean_ctor_get(v___x_1835_, 1);
v_ngen_1839_ = lean_ctor_get(v___x_1835_, 2);
v_auxDeclNGen_1840_ = lean_ctor_get(v___x_1835_, 3);
v_traceState_1841_ = lean_ctor_get(v___x_1835_, 4);
v_cache_1842_ = lean_ctor_get(v___x_1835_, 5);
v_messages_1843_ = lean_ctor_get(v___x_1835_, 6);
v_snapshotTasks_1844_ = lean_ctor_get(v___x_1835_, 8);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1846_ = v___x_1835_;
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snapshotTasks_1844_);
lean_inc(v_infoState_1836_);
lean_inc(v_messages_1843_);
lean_inc(v_cache_1842_);
lean_inc(v_traceState_1841_);
lean_inc(v_auxDeclNGen_1840_);
lean_inc(v_ngen_1839_);
lean_inc(v_nextMacroScope_1838_);
lean_inc(v_env_1837_);
lean_dec(v___x_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v_enabled_1848_; lean_object* v_assignment_1849_; lean_object* v_lazyAssignment_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1866_; 
v_enabled_1848_ = lean_ctor_get_uint8(v_infoState_1836_, sizeof(void*)*3);
v_assignment_1849_ = lean_ctor_get(v_infoState_1836_, 0);
v_lazyAssignment_1850_ = lean_ctor_get(v_infoState_1836_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_infoState_1836_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v_infoState_1836_, 2);
lean_dec(v_unused_1867_);
v___x_1852_ = v_infoState_1836_;
v_isShared_1853_ = v_isSharedCheck_1866_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_lazyAssignment_1850_);
lean_inc(v_assignment_1849_);
lean_dec(v_infoState_1836_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1866_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = l_Lean_PersistentArray_push___redArg(v_a_1824_, v_a_1831_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 2, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_assignment_1849_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_lazyAssignment_1850_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v___x_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*3, v_enabled_1848_);
v___x_1856_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 7, v___x_1856_);
v___x_1858_ = v___x_1846_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_env_1837_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_nextMacroScope_1838_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_ngen_1839_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_auxDeclNGen_1840_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_traceState_1841_);
lean_ctor_set(v_reuseFailAlloc_1864_, 5, v_cache_1842_);
lean_ctor_set(v_reuseFailAlloc_1864_, 6, v_messages_1843_);
lean_ctor_set(v_reuseFailAlloc_1864_, 7, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1864_, 8, v_snapshotTasks_1844_);
v___x_1858_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = lean_st_ref_put(v___y_1817_, v___x_1858_);
v___x_1860_ = lean_box(0);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1860_);
v___x_1862_ = v___x_1833_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_a_1824_);
v_a_1870_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1830_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1830_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_1878_, lean_object* v_mkInfoTree_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v_a_1885_, lean_object* v_a_x3f_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1878_, v_mkInfoTree_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v_a_1885_, v_a_x3f_1886_);
lean_dec(v_a_x3f_1886_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1878_);
return v_res_1888_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_unsigned_to_nat(32u);
v___x_1890_ = lean_mk_empty_array_with_capacity(v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1892_ = ((size_t)5ULL);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_unsigned_to_nat(32u);
v___x_1895_ = lean_mk_empty_array_with_capacity(v___x_1894_);
v___x_1896_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_1897_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___x_1895_);
lean_ctor_set(v___x_1897_, 2, v___x_1893_);
lean_ctor_set(v___x_1897_, 3, v___x_1893_);
lean_ctor_set_usize(v___x_1897_, 4, v___x_1892_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_infoState_1901_; lean_object* v_trees_1902_; lean_object* v___x_1903_; lean_object* v_infoState_1904_; lean_object* v_env_1905_; lean_object* v_nextMacroScope_1906_; lean_object* v_ngen_1907_; lean_object* v_auxDeclNGen_1908_; lean_object* v_traceState_1909_; lean_object* v_cache_1910_; lean_object* v_messages_1911_; lean_object* v_snapshotTasks_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1933_; 
v___x_1900_ = lean_st_ref_get(v___y_1898_);
v_infoState_1901_ = lean_ctor_get(v___x_1900_, 7);
lean_inc_ref(v_infoState_1901_);
lean_dec(v___x_1900_);
v_trees_1902_ = lean_ctor_get(v_infoState_1901_, 2);
lean_inc_ref(v_trees_1902_);
lean_dec_ref(v_infoState_1901_);
v___x_1903_ = lean_st_ref_take(v___y_1898_);
v_infoState_1904_ = lean_ctor_get(v___x_1903_, 7);
v_env_1905_ = lean_ctor_get(v___x_1903_, 0);
v_nextMacroScope_1906_ = lean_ctor_get(v___x_1903_, 1);
v_ngen_1907_ = lean_ctor_get(v___x_1903_, 2);
v_auxDeclNGen_1908_ = lean_ctor_get(v___x_1903_, 3);
v_traceState_1909_ = lean_ctor_get(v___x_1903_, 4);
v_cache_1910_ = lean_ctor_get(v___x_1903_, 5);
v_messages_1911_ = lean_ctor_get(v___x_1903_, 6);
v_snapshotTasks_1912_ = lean_ctor_get(v___x_1903_, 8);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1914_ = v___x_1903_;
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snapshotTasks_1912_);
lean_inc(v_infoState_1904_);
lean_inc(v_messages_1911_);
lean_inc(v_cache_1910_);
lean_inc(v_traceState_1909_);
lean_inc(v_auxDeclNGen_1908_);
lean_inc(v_ngen_1907_);
lean_inc(v_nextMacroScope_1906_);
lean_inc(v_env_1905_);
lean_dec(v___x_1903_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1933_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint8_t v_enabled_1916_; lean_object* v_assignment_1917_; lean_object* v_lazyAssignment_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1931_; 
v_enabled_1916_ = lean_ctor_get_uint8(v_infoState_1904_, sizeof(void*)*3);
v_assignment_1917_ = lean_ctor_get(v_infoState_1904_, 0);
v_lazyAssignment_1918_ = lean_ctor_get(v_infoState_1904_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_infoState_1904_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_infoState_1904_, 2);
lean_dec(v_unused_1932_);
v___x_1920_ = v_infoState_1904_;
v_isShared_1921_ = v_isSharedCheck_1931_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_lazyAssignment_1918_);
lean_inc(v_assignment_1917_);
lean_dec(v_infoState_1904_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1931_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 2, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_assignment_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_lazyAssignment_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v___x_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*3, v_enabled_1916_);
v___x_1924_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 7, v___x_1924_);
v___x_1926_ = v___x_1914_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_env_1905_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_nextMacroScope_1906_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_ngen_1907_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_auxDeclNGen_1908_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_traceState_1909_);
lean_ctor_set(v_reuseFailAlloc_1929_, 5, v_cache_1910_);
lean_ctor_set(v_reuseFailAlloc_1929_, 6, v_messages_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 7, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 8, v_snapshotTasks_1912_);
v___x_1926_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_st_ref_put(v___y_1898_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_trees_1902_);
return v___x_1928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1934_);
lean_dec(v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_1937_, lean_object* v_mkInfoTree_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v_infoState_1947_; uint8_t v_enabled_1948_; 
v___x_1946_ = lean_st_ref_get(v___y_1944_);
v_infoState_1947_ = lean_ctor_get(v___x_1946_, 7);
lean_inc_ref(v_infoState_1947_);
lean_dec(v___x_1946_);
v_enabled_1948_ = lean_ctor_get_uint8(v_infoState_1947_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1947_);
if (v_enabled_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec_ref(v_mkInfoTree_1938_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
v___x_1949_ = lean_apply_7(v_x_1937_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v_r_1952_; 
v___x_1950_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1944_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
v_r_1952_ = lean_apply_7(v_x_1937_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
if (lean_obj_tag(v_r_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1977_; 
v_a_1953_ = lean_ctor_get(v_r_1952_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_r_1952_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1955_ = v_r_1952_;
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v_r_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1977_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
lean_inc(v_a_1953_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 1);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1944_, v_mkInfoTree_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v_a_1951_, v___x_1958_);
lean_dec_ref(v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1967_);
v___x_1961_ = v___x_1959_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v___x_1959_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v_a_1953_);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1953_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_a_1953_);
v_a_1968_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1959_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1959_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_a_1978_ = lean_ctor_get(v_r_1952_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v_r_1952_, 1);
v___x_1979_ = lean_box(0);
v___x_1980_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1944_, v_mkInfoTree_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v_a_1951_, v___x_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1980_, 0);
lean_dec(v_unused_1988_);
v___x_1982_ = v___x_1980_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v___x_1980_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 1);
lean_ctor_set(v___x_1982_, 0, v_a_1978_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1978_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1978_);
v_a_1989_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1980_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_1997_, lean_object* v_mkInfoTree_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_1997_, v_mkInfoTree_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2007_, lean_object* v_output_2008_, lean_object* v_trees_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_lctx_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_lctx_2017_ = lean_ctor_get(v___y_2012_, 2);
lean_inc_ref(v_lctx_2017_);
v___x_2018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2018_, 0, v_lctx_2017_);
lean_ctor_set(v___x_2018_, 1, v_stx_2007_);
lean_ctor_set(v___x_2018_, 2, v_output_2008_);
v___x_2019_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_trees_2009_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2022_, lean_object* v_output_2023_, lean_object* v_trees_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2022_, v_output_2023_, v_trees_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2033_, lean_object* v_output_2034_, lean_object* v_x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___f_2043_; lean_object* v___x_2044_; 
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2043_, 0, v_stx_2033_);
lean_closure_set(v___f_2043_, 1, v_output_2034_);
v___x_2044_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2035_, v___f_2043_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2045_, lean_object* v_output_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2045_, v_output_2046_, v_x_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2056_, lean_object* v_afterStx_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_inc_ref(v___y_2059_);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2067_, 0, v_x_2058_);
lean_closure_set(v___f_2067_, 1, v___y_2059_);
lean_inc(v_afterStx_2057_);
lean_inc(v_beforeStx_2056_);
v___x_2068_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2068_, 0, lean_box(0));
lean_closure_set(v___x_2068_, 1, v_beforeStx_2056_);
lean_closure_set(v___x_2068_, 2, v_afterStx_2057_);
lean_closure_set(v___x_2068_, 3, v___f_2067_);
v___x_2069_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2056_, v_afterStx_2057_, v___x_2068_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2069_) == 0)
{
return v___x_2069_;
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2078_, lean_object* v_afterStx_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2078_, v_afterStx_2079_, v_x_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2089_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2093_ = l_String_toRawSubstring_x27(v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2115_, uint8_t v___x_2116_, lean_object* v_config_2117_, lean_object* v_a_2118_, uint8_t v___x_2119_, lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v___f_2123_, lean_object* v___x_2124_, lean_object* v_body_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_term_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v_ref_2142_; lean_object* v___y_2143_; lean_object* v_toCold_2149_; lean_object* v_ref_2150_; lean_object* v_quotContext_2151_; lean_object* v_currMacroScope_2152_; lean_object* v_ref_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_eq_x3f_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_toCold_2149_ = lean_ctor_get(v___y_2131_, 0);
v_ref_2150_ = lean_ctor_get(v___y_2131_, 2);
v_quotContext_2151_ = lean_ctor_get(v_toCold_2149_, 8);
v_currMacroScope_2152_ = lean_ctor_get(v_toCold_2149_, 9);
v_ref_2153_ = l_Lean_replaceRef(v_rhs_2115_, v_ref_2150_);
v___x_2154_ = l_Lean_SourceInfo_fromRef(v_ref_2153_, v___x_2116_);
lean_dec(v_ref_2153_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2154_, 2);
v___x_2156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2158_ = lean_ctor_get(v_config_2117_, 0);
lean_inc(v_eq_x3f_2158_);
lean_dec_ref(v_config_2117_);
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2152_);
lean_inc(v_quotContext_2151_);
v___x_2160_ = l_Lean_addMacroScope(v_quotContext_2151_, v___x_2159_, v_currMacroScope_2152_);
v___x_2161_ = lean_box(0);
lean_inc(v___x_2160_);
v___x_2162_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2154_);
lean_ctor_set(v___x_2162_, 1, v___x_2157_);
lean_ctor_set(v___x_2162_, 2, v___x_2160_);
lean_ctor_set(v___x_2162_, 3, v___x_2161_);
v___x_2163_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2122_);
lean_inc_ref(v___x_2121_);
lean_inc_ref(v___x_2120_);
v___x_2164_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node2(v___x_2154_, v___x_2164_, v___x_2156_, v___x_2162_);
if (lean_obj_tag(v_eq_x3f_2158_) == 1)
{
lean_object* v_val_2166_; lean_object* v___x_2167_; 
v_val_2166_ = lean_ctor_get(v_eq_x3f_2158_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_eq_x3f_2158_, 1);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc_ref(v___y_2126_);
lean_inc(v_ref_2150_);
v___x_2167_ = lean_apply_9(v___f_2123_, v_ref_2150_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, lean_box(0));
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_n(v_a_2168_, 23);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2122_, 5);
lean_inc_ref_n(v___x_2121_, 5);
lean_inc_ref_n(v___x_2120_, 5);
v___x_2170_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2169_);
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2168_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2173_, 0, v_a_2168_);
lean_ctor_set(v___x_2173_, 1, v___x_2155_);
v___x_2174_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2174_, 0, v_a_2168_);
lean_ctor_set(v___x_2174_, 1, v___x_2157_);
lean_ctor_set(v___x_2174_, 2, v___x_2160_);
lean_ctor_set(v___x_2174_, 3, v___x_2161_);
v___x_2175_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2168_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_a_2168_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2180_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2168_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2184_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2168_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2187_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2168_);
lean_ctor_set(v___x_2188_, 1, v___x_2186_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2190_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2168_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_Syntax_node2(v_a_2168_, v___x_2186_, v_val_2166_, v___x_2192_);
v___x_2194_ = l_Lean_Syntax_node2(v_a_2168_, v___x_2190_, v___x_2193_, v___x_2165_);
v___x_2195_ = l_Lean_Syntax_node1(v_a_2168_, v___x_2186_, v___x_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2168_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2199_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2201_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2200_);
v___x_2202_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2168_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Lean_Syntax_node1(v_a_2168_, v___x_2186_, v___x_2124_);
v___x_2205_ = l_Lean_Syntax_node1(v_a_2168_, v___x_2186_, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_a_2168_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = l_Lean_Syntax_node4(v_a_2168_, v___x_2201_, v___x_2203_, v___x_2205_, v___x_2207_, v_body_2125_);
v___x_2209_ = l_Lean_Syntax_node1(v_a_2168_, v___x_2186_, v___x_2208_);
v___x_2210_ = l_Lean_Syntax_node1(v_a_2168_, v___x_2199_, v___x_2209_);
lean_inc_ref(v___x_2188_);
v___x_2211_ = l_Lean_Syntax_node6(v_a_2168_, v___x_2184_, v___x_2185_, v___x_2188_, v___x_2188_, v___x_2195_, v___x_2197_, v___x_2210_);
lean_inc_ref(v___x_2178_);
lean_inc_ref(v___x_2174_);
lean_inc_ref(v___x_2173_);
v___x_2212_ = l_Lean_Syntax_node5(v_a_2168_, v___x_2180_, v___x_2182_, v___x_2173_, v___x_2174_, v___x_2178_, v___x_2211_);
v___x_2213_ = l_Lean_Syntax_node7(v_a_2168_, v___x_2170_, v___x_2172_, v___x_2173_, v___x_2174_, v___x_2176_, v_rhs_2115_, v___x_2178_, v___x_2212_);
lean_inc(v_ref_2150_);
v_term_2135_ = v___x_2213_;
v___y_2136_ = v___y_2126_;
v___y_2137_ = v___y_2127_;
v___y_2138_ = v___y_2128_;
v___y_2139_ = v___y_2129_;
v___y_2140_ = v___y_2130_;
v___y_2141_ = v___y_2131_;
v_ref_2142_ = v_ref_2150_;
v___y_2143_ = v___y_2132_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_val_2166_);
lean_dec(v___x_2165_);
lean_dec(v___x_2160_);
lean_dec(v_body_2125_);
lean_dec(v___x_2124_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_a_2118_);
lean_dec(v_rhs_2115_);
v_a_2214_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2167_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2167_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v___x_2222_; 
lean_dec(v_eq_x3f_2158_);
lean_inc_ref(v_a_2118_);
v___x_2222_ = l_Lean_Elab_Term_exprToSyntax(v_a_2118_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc_ref(v___y_2126_);
lean_inc(v_ref_2150_);
v___x_2224_ = lean_apply_9(v___f_2123_, v_ref_2150_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, lean_box(0));
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc_n(v_a_2225_, 32);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2122_, 8);
lean_inc_ref_n(v___x_2121_, 8);
lean_inc_ref_n(v___x_2120_, 8);
v___x_2227_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2226_);
v___x_2228_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2225_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2225_);
lean_ctor_set(v___x_2230_, 1, v___x_2155_);
v___x_2231_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2225_);
lean_ctor_set(v___x_2231_, 1, v___x_2157_);
lean_ctor_set(v___x_2231_, 2, v___x_2160_);
lean_ctor_set(v___x_2231_, 3, v___x_2161_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_a_2225_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_a_2225_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2237_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2225_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2241_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2225_);
lean_ctor_set(v___x_2242_, 1, v___x_2240_);
v___x_2243_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2244_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2245_, 0, v_a_2225_);
lean_ctor_set(v___x_2245_, 1, v___x_2243_);
lean_ctor_set(v___x_2245_, 2, v___x_2244_);
v___x_2246_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2247_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_a_2225_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2225_);
lean_ctor_set(v___x_2250_, 1, v___x_2246_);
v___x_2251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2252_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2225_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2256_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_a_2225_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2256_, v___x_2258_);
v___x_2260_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2259_);
v___x_2261_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_a_2225_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
lean_inc_ref_n(v___x_2245_, 2);
v___x_2263_ = l_Lean_Syntax_node5(v_a_2225_, v___x_2252_, v___x_2254_, v___x_2260_, v___x_2245_, v___x_2262_, v_a_2223_);
v___x_2264_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2265_, 0, v_a_2225_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
lean_inc_ref(v___x_2233_);
v___x_2266_ = l_Lean_Syntax_node5(v_a_2225_, v___x_2247_, v___x_2249_, v___x_2250_, v___x_2233_, v___x_2263_, v___x_2265_);
v___x_2267_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2266_);
v___x_2268_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2269_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2268_);
v___x_2270_ = l_Lean_Syntax_node2(v_a_2225_, v___x_2269_, v___x_2245_, v___x_2165_);
v___x_2271_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2225_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2275_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2277_ = l_Lean_Name_mkStr4(v___x_2120_, v___x_2121_, v___x_2122_, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2225_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2124_);
v___x_2281_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2280_);
v___x_2282_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2225_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_Syntax_node4(v_a_2225_, v___x_2277_, v___x_2279_, v___x_2281_, v___x_2283_, v_body_2125_);
v___x_2285_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2243_, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_node1(v_a_2225_, v___x_2275_, v___x_2285_);
v___x_2287_ = l_Lean_Syntax_node6(v_a_2225_, v___x_2241_, v___x_2242_, v___x_2245_, v___x_2267_, v___x_2271_, v___x_2273_, v___x_2286_);
lean_inc_ref(v___x_2235_);
lean_inc_ref(v___x_2231_);
lean_inc_ref(v___x_2230_);
v___x_2288_ = l_Lean_Syntax_node5(v_a_2225_, v___x_2237_, v___x_2239_, v___x_2230_, v___x_2231_, v___x_2235_, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node7(v_a_2225_, v___x_2227_, v___x_2229_, v___x_2230_, v___x_2231_, v___x_2233_, v_rhs_2115_, v___x_2235_, v___x_2288_);
lean_inc(v_ref_2150_);
v_term_2135_ = v___x_2289_;
v___y_2136_ = v___y_2126_;
v___y_2137_ = v___y_2127_;
v___y_2138_ = v___y_2128_;
v___y_2139_ = v___y_2129_;
v___y_2140_ = v___y_2130_;
v___y_2141_ = v___y_2131_;
v_ref_2142_ = v_ref_2150_;
v___y_2143_ = v___y_2132_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2223_);
lean_dec(v___x_2165_);
lean_dec(v___x_2160_);
lean_dec(v_body_2125_);
lean_dec(v___x_2124_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_a_2118_);
lean_dec(v_rhs_2115_);
v_a_2290_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2224_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2224_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v___x_2165_);
lean_dec(v___x_2160_);
lean_dec(v_body_2125_);
lean_dec(v___x_2124_);
lean_dec_ref(v___f_2123_);
lean_dec_ref(v___x_2122_);
lean_dec_ref(v___x_2121_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_a_2118_);
lean_dec(v_rhs_2115_);
v_a_2298_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2222_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2222_);
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
v___jp_2134_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; 
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_a_2118_);
v___x_2145_ = lean_box(0);
v___x_2146_ = lean_box(v___x_2119_);
lean_inc(v_term_2135_);
v___f_2147_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2147_, 0, v_term_2135_);
lean_closure_set(v___f_2147_, 1, v___x_2144_);
lean_closure_set(v___f_2147_, 2, v___x_2146_);
lean_closure_set(v___f_2147_, 3, v___x_2145_);
v___x_2148_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2142_, v_term_2135_, v___f_2147_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2143_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2306_ = _args[0];
lean_object* v___x_2307_ = _args[1];
lean_object* v_config_2308_ = _args[2];
lean_object* v_a_2309_ = _args[3];
lean_object* v___x_2310_ = _args[4];
lean_object* v___x_2311_ = _args[5];
lean_object* v___x_2312_ = _args[6];
lean_object* v___x_2313_ = _args[7];
lean_object* v___f_2314_ = _args[8];
lean_object* v___x_2315_ = _args[9];
lean_object* v_body_2316_ = _args[10];
lean_object* v___y_2317_ = _args[11];
lean_object* v___y_2318_ = _args[12];
lean_object* v___y_2319_ = _args[13];
lean_object* v___y_2320_ = _args[14];
lean_object* v___y_2321_ = _args[15];
lean_object* v___y_2322_ = _args[16];
lean_object* v___y_2323_ = _args[17];
lean_object* v___y_2324_ = _args[18];
_start:
{
uint8_t v___x_87311__boxed_2325_; uint8_t v___x_87313__boxed_2326_; lean_object* v_res_2327_; 
v___x_87311__boxed_2325_ = lean_unbox(v___x_2307_);
v___x_87313__boxed_2326_ = lean_unbox(v___x_2310_);
v_res_2327_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2306_, v___x_87311__boxed_2325_, v_config_2308_, v_a_2309_, v___x_87313__boxed_2326_, v___x_2311_, v___x_2312_, v___x_2313_, v___f_2314_, v___x_2315_, v_body_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2328_, lean_object* v___y_2329_){
_start:
{
if (lean_obj_tag(v_x_2328_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v_x_2328_, 0);
lean_inc(v_a_2330_);
v___x_2331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2330_);
lean_ctor_set(v___x_2331_, 1, v___y_2329_);
return v___x_2331_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v_x_2328_, 0);
lean_inc(v_a_2332_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2332_);
lean_ctor_set(v___x_2333_, 1, v___y_2329_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2334_, v___y_2335_);
lean_dec_ref(v_x_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2337_, lean_object* v_stx_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2337_, v_stx_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
if (lean_obj_tag(v_a_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2351_; 
v_a_2343_ = lean_ctor_get(v___x_2341_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2341_, 0);
lean_dec(v_unused_2352_);
v___x_2345_ = v___x_2341_;
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2341_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = lean_box(0);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_a_2343_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2381_; 
v_val_2353_ = lean_ctor_get(v_a_2342_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_a_2342_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2355_ = v_a_2342_;
v_isShared_2356_ = v_isSharedCheck_2381_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_dec(v_a_2342_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2381_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_snd_2357_; 
v_snd_2357_ = lean_ctor_get(v_val_2353_, 1);
lean_inc(v_snd_2357_);
lean_dec(v_val_2353_);
if (lean_obj_tag(v_snd_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2367_; 
lean_del_object(v___x_2355_);
v_a_2358_ = lean_ctor_get(v___x_2341_, 1);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2341_, 2);
v_a_2359_ = lean_ctor_get(v_snd_2357_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_snd_2357_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2361_ = v_snd_2357_;
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v_snd_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2364_, v_a_2358_);
lean_dec_ref(v___x_2364_);
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2380_; 
v_a_2368_ = lean_ctor_get(v___x_2341_, 1);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2341_, 2);
v_a_2369_ = lean_ctor_get(v_snd_2357_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_snd_2357_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2371_ = v_snd_2357_;
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v_snd_2357_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v_a_2369_);
v___x_2374_ = v___x_2355_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2374_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2376_, v_a_2368_);
lean_dec_ref(v___x_2376_);
return v___x_2377_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_a_2382_ = lean_ctor_get(v___x_2341_, 0);
v_a_2383_ = lean_ctor_get(v___x_2341_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2341_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_inc(v_a_2382_);
lean_dec(v___x_2341_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2391_, lean_object* v_stx_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2391_, v_stx_2392_, v___y_2393_, v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_currNamespace_2396_);
lean_ctor_set(v___x_2399_, 1, v___y_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2404_, lean_object* v_currNamespace_2405_, lean_object* v_openDecls_2406_, lean_object* v_n_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = l_Lean_ResolveName_resolveNamespace(v_env_2404_, v_currNamespace_2405_, v_openDecls_2406_, v_n_2407_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___y_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2412_, lean_object* v_currNamespace_2413_, lean_object* v_openDecls_2414_, lean_object* v_n_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2412_, v_currNamespace_2413_, v_openDecls_2414_, v_n_2415_, v___y_2416_, v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2419_, lean_object* v_declName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_2423_; lean_object* v_env_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2423_ = 0;
v_env_2424_ = l_Lean_Environment_setExporting(v_env_2419_, v___x_2423_);
lean_inc(v_declName_2420_);
v___x_2425_ = l_Lean_mkPrivateName(v_env_2424_, v_declName_2420_);
v___x_2426_ = 1;
lean_inc_ref(v_env_2424_);
v___x_2427_ = l_Lean_Environment_contains(v_env_2424_, v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = l_Lean_privateToUserName(v_declName_2420_);
v___x_2429_ = l_Lean_Environment_contains(v_env_2424_, v___x_2428_, v___x_2426_);
v___x_2430_ = lean_box(v___x_2429_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___y_2422_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec_ref(v_env_2424_);
lean_dec(v_declName_2420_);
v___x_2432_ = lean_box(v___x_2427_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___y_2422_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2434_, lean_object* v_declName_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2434_, v_declName_2435_, v___y_2436_, v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2438_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2439_; double v___x_2440_; 
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_float_of_nat(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_ref_2450_; lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2496_; 
v_ref_2450_ = lean_ctor_get(v___y_2447_, 2);
v___x_2451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2496_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2496_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v_traceState_2457_; lean_object* v_env_2458_; lean_object* v_nextMacroScope_2459_; lean_object* v_ngen_2460_; lean_object* v_auxDeclNGen_2461_; lean_object* v_cache_2462_; lean_object* v_messages_2463_; lean_object* v_infoState_2464_; lean_object* v_snapshotTasks_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2495_; 
v___x_2456_ = lean_st_ref_take(v___y_2448_);
v_traceState_2457_ = lean_ctor_get(v___x_2456_, 4);
v_env_2458_ = lean_ctor_get(v___x_2456_, 0);
v_nextMacroScope_2459_ = lean_ctor_get(v___x_2456_, 1);
v_ngen_2460_ = lean_ctor_get(v___x_2456_, 2);
v_auxDeclNGen_2461_ = lean_ctor_get(v___x_2456_, 3);
v_cache_2462_ = lean_ctor_get(v___x_2456_, 5);
v_messages_2463_ = lean_ctor_get(v___x_2456_, 6);
v_infoState_2464_ = lean_ctor_get(v___x_2456_, 7);
v_snapshotTasks_2465_ = lean_ctor_get(v___x_2456_, 8);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2467_ = v___x_2456_;
v_isShared_2468_ = v_isSharedCheck_2495_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snapshotTasks_2465_);
lean_inc(v_infoState_2464_);
lean_inc(v_messages_2463_);
lean_inc(v_cache_2462_);
lean_inc(v_traceState_2457_);
lean_inc(v_auxDeclNGen_2461_);
lean_inc(v_ngen_2460_);
lean_inc(v_nextMacroScope_2459_);
lean_inc(v_env_2458_);
lean_dec(v___x_2456_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2495_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
uint64_t v_tid_2469_; lean_object* v_traces_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2494_; 
v_tid_2469_ = lean_ctor_get_uint64(v_traceState_2457_, sizeof(void*)*1);
v_traces_2470_ = lean_ctor_get(v_traceState_2457_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_traceState_2457_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2472_ = v_traceState_2457_;
v_isShared_2473_ = v_isSharedCheck_2494_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_traces_2470_);
lean_dec(v_traceState_2457_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2494_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; double v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2476_ = 0;
v___x_2477_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2478_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2478_, 0, v_cls_2443_);
lean_ctor_set(v___x_2478_, 1, v___x_2474_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
lean_ctor_set_float(v___x_2478_, sizeof(void*)*3, v___x_2475_);
lean_ctor_set_float(v___x_2478_, sizeof(void*)*3 + 8, v___x_2475_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*3 + 16, v___x_2476_);
v___x_2479_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2480_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v_a_2452_);
lean_ctor_set(v___x_2480_, 2, v___x_2479_);
lean_inc(v_ref_2450_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_ref_2450_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_Lean_PersistentArray_push___redArg(v_traces_2470_, v___x_2481_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2482_);
v___x_2484_ = v___x_2472_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2482_);
lean_ctor_set_uint64(v_reuseFailAlloc_2493_, sizeof(void*)*1, v_tid_2469_);
v___x_2484_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2486_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v___x_2484_);
v___x_2486_ = v___x_2467_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_env_2458_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2459_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2460_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_cache_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_messages_2463_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_infoState_2464_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_snapshotTasks_2465_);
v___x_2486_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = lean_st_ref_put(v___y_2448_, v___x_2486_);
v___x_2488_ = lean_box(0);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2488_);
v___x_2490_ = v___x_2454_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2497_, lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2497_, v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
if (lean_obj_tag(v_as_2508_) == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
else
{
lean_object* v_toCold_2519_; lean_object* v_options_2520_; uint8_t v_hasTrace_2521_; 
v_toCold_2519_ = lean_ctor_get(v___y_2514_, 0);
v_options_2520_ = lean_ctor_get(v_toCold_2519_, 2);
v_hasTrace_2521_ = lean_ctor_get_uint8(v_options_2520_, sizeof(void*)*1);
if (v_hasTrace_2521_ == 0)
{
lean_object* v_tail_2522_; 
v_tail_2522_ = lean_ctor_get(v_as_2508_, 1);
lean_inc(v_tail_2522_);
lean_dec_ref_known(v_as_2508_, 2);
v_as_2508_ = v_tail_2522_;
goto _start;
}
else
{
lean_object* v_head_2524_; lean_object* v_tail_2525_; lean_object* v_fst_2526_; lean_object* v_snd_2527_; lean_object* v_inheritedTraceOptions_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_head_2524_ = lean_ctor_get(v_as_2508_, 0);
lean_inc(v_head_2524_);
v_tail_2525_ = lean_ctor_get(v_as_2508_, 1);
lean_inc(v_tail_2525_);
lean_dec_ref_known(v_as_2508_, 2);
v_fst_2526_ = lean_ctor_get(v_head_2524_, 0);
lean_inc_n(v_fst_2526_, 2);
v_snd_2527_ = lean_ctor_get(v_head_2524_, 1);
lean_inc(v_snd_2527_);
lean_dec(v_head_2524_);
v_inheritedTraceOptions_2528_ = lean_ctor_get(v_toCold_2519_, 11);
v___x_2529_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2530_ = l_Lean_Name_append(v___x_2529_, v_fst_2526_);
v___x_2531_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2528_, v_options_2520_, v___x_2530_);
lean_dec(v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec(v_snd_2527_);
lean_dec(v_fst_2526_);
v_as_2508_ = v_tail_2525_;
goto _start;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_snd_2527_);
v___x_2534_ = l_Lean_MessageData_ofFormat(v___x_2533_);
v___x_2535_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2526_, v___x_2534_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref_known(v___x_2535_, 1);
v_as_2508_ = v_tail_2525_;
goto _start;
}
else
{
lean_dec(v_tail_2525_);
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2546_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2547_, lean_object* v_i_2548_, lean_object* v_k_2549_){
_start:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = lean_array_get_size(v_keys_2547_);
v___x_2551_ = lean_nat_dec_lt(v_i_2548_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_dec(v_i_2548_);
return v___x_2551_;
}
else
{
lean_object* v_k_x27_2552_; uint8_t v___x_2553_; 
v_k_x27_2552_ = lean_array_fget_borrowed(v_keys_2547_, v_i_2548_);
v___x_2553_ = l_Lean_instBEqExtraModUse_beq(v_k_2549_, v_k_x27_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v_i_2548_, v___x_2554_);
lean_dec(v_i_2548_);
v_i_2548_ = v___x_2555_;
goto _start;
}
else
{
lean_dec(v_i_2548_);
return v___x_2551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2557_, lean_object* v_i_2558_, lean_object* v_k_2559_){
_start:
{
uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_res_2560_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2557_, v_i_2558_, v_k_2559_);
lean_dec_ref(v_k_2559_);
lean_dec_ref(v_keys_2557_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2562_, size_t v_x_2563_, lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2562_) == 0)
{
lean_object* v_es_2565_; lean_object* v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; lean_object* v_j_2569_; lean_object* v___x_2570_; 
v_es_2565_ = lean_ctor_get(v_x_2562_, 0);
v___x_2566_ = lean_box(2);
v___x_2567_ = ((size_t)31ULL);
v___x_2568_ = lean_usize_land(v_x_2563_, v___x_2567_);
v_j_2569_ = lean_usize_to_nat(v___x_2568_);
v___x_2570_ = lean_array_get_borrowed(v___x_2566_, v_es_2565_, v_j_2569_);
lean_dec(v_j_2569_);
switch(lean_obj_tag(v___x_2570_))
{
case 0:
{
lean_object* v_key_2571_; uint8_t v___x_2572_; 
v_key_2571_ = lean_ctor_get(v___x_2570_, 0);
v___x_2572_ = l_Lean_instBEqExtraModUse_beq(v_x_2564_, v_key_2571_);
return v___x_2572_;
}
case 1:
{
lean_object* v_node_2573_; size_t v___x_2574_; size_t v___x_2575_; 
v_node_2573_ = lean_ctor_get(v___x_2570_, 0);
v___x_2574_ = ((size_t)5ULL);
v___x_2575_ = lean_usize_shift_right(v_x_2563_, v___x_2574_);
v_x_2562_ = v_node_2573_;
v_x_2563_ = v___x_2575_;
goto _start;
}
default: 
{
uint8_t v___x_2577_; 
v___x_2577_ = 0;
return v___x_2577_;
}
}
}
else
{
lean_object* v_ks_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v_ks_2578_ = lean_ctor_get(v_x_2562_, 0);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2578_, v___x_2579_, v_x_2564_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_){
_start:
{
size_t v_x_88055__boxed_2584_; uint8_t v_res_2585_; lean_object* v_r_2586_; 
v_x_88055__boxed_2584_ = lean_unbox_usize(v_x_2582_);
lean_dec(v_x_2582_);
v_res_2585_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2581_, v_x_88055__boxed_2584_, v_x_2583_);
lean_dec_ref(v_x_2583_);
lean_dec_ref(v_x_2581_);
v_r_2586_ = lean_box(v_res_2585_);
return v_r_2586_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2587_, lean_object* v_x_2588_){
_start:
{
uint64_t v___x_2589_; size_t v___x_2590_; uint8_t v___x_2591_; 
v___x_2589_ = l_Lean_instHashableExtraModUse_hash(v_x_2588_);
v___x_2590_ = lean_uint64_to_usize(v___x_2589_);
v___x_2591_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2587_, v___x_2590_, v_x_2588_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2592_, lean_object* v_x_2593_){
_start:
{
uint8_t v_res_2594_; lean_object* v_r_2595_; 
v_res_2594_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2592_, v_x_2593_);
lean_dec_ref(v_x_2593_);
lean_dec_ref(v_x_2592_);
v_r_2595_ = lean_box(v_res_2594_);
return v_r_2595_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2599_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2600_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2599_, v___x_2598_);
return v___x_2600_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2607_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
lean_ctor_set(v___x_2607_, 3, v___x_2606_);
lean_ctor_set(v___x_2607_, 4, v___x_2606_);
lean_ctor_set(v___x_2607_, 5, v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
return v___x_2618_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_cls_2619_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2620_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2621_ = l_Lean_Name_append(v___x_2620_, v_cls_2619_);
return v___x_2621_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2632_, uint8_t v_isMeta_2633_, lean_object* v_hint_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; lean_object* v_env_2644_; uint8_t v_isExporting_2645_; lean_object* v___x_2646_; lean_object* v_env_2647_; lean_object* v___x_2648_; lean_object* v_entry_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2643_ = lean_st_ref_get(v___y_2641_);
v_env_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc_ref(v_env_2644_);
lean_dec(v___x_2643_);
v_isExporting_2645_ = lean_ctor_get_uint8(v_env_2644_, sizeof(void*)*8);
lean_dec_ref(v_env_2644_);
v___x_2646_ = lean_st_ref_get(v___y_2641_);
v_env_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc_ref(v_env_2647_);
lean_dec(v___x_2646_);
v___x_2648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2632_);
v_entry_2649_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2649_, 0, v_mod_2632_);
lean_ctor_set_uint8(v_entry_2649_, sizeof(void*)*1, v_isExporting_2645_);
lean_ctor_set_uint8(v_entry_2649_, sizeof(void*)*1 + 1, v_isMeta_2633_);
v___x_2650_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2651_ = lean_box(1);
v___x_2652_ = lean_box(0);
v___x_2695_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2648_, v___x_2650_, v_env_2647_, v___x_2651_, v___x_2652_);
v___x_2696_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2695_, v_entry_2649_);
lean_dec(v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v_toCold_2697_; lean_object* v_options_2698_; uint8_t v_hasTrace_2699_; 
v_toCold_2697_ = lean_ctor_get(v___y_2640_, 0);
v_options_2698_ = lean_ctor_get(v_toCold_2697_, 2);
v_hasTrace_2699_ = lean_ctor_get_uint8(v_options_2698_, sizeof(void*)*1);
if (v_hasTrace_2699_ == 0)
{
lean_dec(v_hint_2634_);
lean_dec(v_mod_2632_);
v___y_2654_ = v___y_2639_;
v___y_2655_ = v___y_2641_;
goto v___jp_2653_;
}
else
{
lean_object* v_inheritedTraceOptions_2700_; lean_object* v_cls_2701_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_inheritedTraceOptions_2700_ = lean_ctor_get(v_toCold_2697_, 11);
v_cls_2701_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2721_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2700_, v_options_2698_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_dec(v_hint_2634_);
lean_dec(v_mod_2632_);
v___y_2654_ = v___y_2639_;
v___y_2655_ = v___y_2641_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2723_; lean_object* v___y_2725_; 
v___x_2723_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2645_ == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2725_ = v___x_2732_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2725_ = v___x_2733_;
goto v___jp_2724_;
}
v___jp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_inc_ref(v___y_2725_);
v___x_2726_ = l_Lean_stringToMessageData(v___y_2725_);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2723_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
if (v_isMeta_2633_ == 0)
{
lean_object* v___x_2730_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2708_ = v___x_2729_;
v___y_2709_ = v___x_2730_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2731_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2708_ = v___x_2729_;
v___y_2709_ = v___x_2731_;
goto v___jp_2707_;
}
}
}
v___jp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___y_2703_);
lean_ctor_set(v___x_2705_, 1, v___y_2704_);
v___x_2706_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2701_, v___x_2705_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_dec_ref_known(v___x_2706_, 1);
v___y_2654_ = v___y_2639_;
v___y_2655_ = v___y_2641_;
goto v___jp_2653_;
}
else
{
lean_dec_ref_known(v_entry_2649_, 1);
return v___x_2706_;
}
}
v___jp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
lean_inc_ref(v___y_2709_);
v___x_2710_ = l_Lean_stringToMessageData(v___y_2709_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___y_2708_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofName(v_mod_2632_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Lean_Name_isAnonymous(v_hint_2634_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2718_ = l_Lean_MessageData_ofName(v_hint_2634_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___y_2703_ = v___x_2715_;
v___y_2704_ = v___x_2719_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2720_; 
lean_dec(v_hint_2634_);
v___x_2720_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2703_ = v___x_2715_;
v___y_2704_ = v___x_2720_;
goto v___jp_2702_;
}
}
}
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_dec_ref_known(v_entry_2649_, 1);
lean_dec(v_hint_2634_);
lean_dec(v_mod_2632_);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
v___jp_2653_:
{
lean_object* v___x_2656_; lean_object* v_toEnvExtension_2657_; lean_object* v_env_2658_; lean_object* v_nextMacroScope_2659_; lean_object* v_ngen_2660_; lean_object* v_auxDeclNGen_2661_; lean_object* v_traceState_2662_; lean_object* v_messages_2663_; lean_object* v_infoState_2664_; lean_object* v_snapshotTasks_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2693_; 
v___x_2656_ = lean_st_ref_take(v___y_2655_);
v_toEnvExtension_2657_ = lean_ctor_get(v___x_2650_, 0);
v_env_2658_ = lean_ctor_get(v___x_2656_, 0);
v_nextMacroScope_2659_ = lean_ctor_get(v___x_2656_, 1);
v_ngen_2660_ = lean_ctor_get(v___x_2656_, 2);
v_auxDeclNGen_2661_ = lean_ctor_get(v___x_2656_, 3);
v_traceState_2662_ = lean_ctor_get(v___x_2656_, 4);
v_messages_2663_ = lean_ctor_get(v___x_2656_, 6);
v_infoState_2664_ = lean_ctor_get(v___x_2656_, 7);
v_snapshotTasks_2665_ = lean_ctor_get(v___x_2656_, 8);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2656_, 5);
lean_dec(v_unused_2694_);
v___x_2667_ = v___x_2656_;
v_isShared_2668_ = v_isSharedCheck_2693_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_snapshotTasks_2665_);
lean_inc(v_infoState_2664_);
lean_inc(v_messages_2663_);
lean_inc(v_traceState_2662_);
lean_inc(v_auxDeclNGen_2661_);
lean_inc(v_ngen_2660_);
lean_inc(v_nextMacroScope_2659_);
lean_inc(v_env_2658_);
lean_dec(v___x_2656_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2693_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_asyncMode_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v_asyncMode_2669_ = lean_ctor_get(v_toEnvExtension_2657_, 2);
v___x_2670_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2650_, v_env_2658_, v_entry_2649_, v_asyncMode_2669_, v___x_2652_);
v___x_2671_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 5, v___x_2671_);
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_nextMacroScope_2659_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_ngen_2660_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_auxDeclNGen_2661_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_traceState_2662_);
lean_ctor_set(v_reuseFailAlloc_2692_, 5, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2692_, 6, v_messages_2663_);
lean_ctor_set(v_reuseFailAlloc_2692_, 7, v_infoState_2664_);
lean_ctor_set(v_reuseFailAlloc_2692_, 8, v_snapshotTasks_2665_);
v___x_2673_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_mctx_2676_; lean_object* v_zetaDeltaFVarIds_2677_; lean_object* v_postponed_2678_; lean_object* v_diag_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2690_; 
v___x_2674_ = lean_st_ref_put(v___y_2655_, v___x_2673_);
v___x_2675_ = lean_st_ref_take(v___y_2654_);
v_mctx_2676_ = lean_ctor_get(v___x_2675_, 0);
v_zetaDeltaFVarIds_2677_ = lean_ctor_get(v___x_2675_, 2);
v_postponed_2678_ = lean_ctor_get(v___x_2675_, 3);
v_diag_2679_ = lean_ctor_get(v___x_2675_, 4);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v___x_2675_, 1);
lean_dec(v_unused_2691_);
v___x_2681_ = v___x_2675_;
v_isShared_2682_ = v_isSharedCheck_2690_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_diag_2679_);
lean_inc(v_postponed_2678_);
lean_inc(v_zetaDeltaFVarIds_2677_);
lean_inc(v_mctx_2676_);
lean_dec(v___x_2675_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2690_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_mctx_2676_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v_zetaDeltaFVarIds_2677_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_postponed_2678_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v_diag_2679_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_st_ref_put(v___y_2654_, v___x_2685_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2736_, lean_object* v_isMeta_2737_, lean_object* v_hint_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v_isMeta_boxed_2747_; lean_object* v_res_2748_; 
v_isMeta_boxed_2747_ = lean_unbox(v_isMeta_2737_);
v_res_2748_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2736_, v_isMeta_boxed_2747_, v_hint_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2749_, lean_object* v_declName_2750_, lean_object* v_as_2751_, size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
lean_dec(v_declName_2750_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_b_2754_);
return v___x_2764_;
}
else
{
lean_object* v___x_2765_; lean_object* v_modules_2766_; lean_object* v___x_2767_; lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v_toImport_2770_; lean_object* v_module_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2765_ = l_Lean_Environment_header(v___x_2749_);
v_modules_2766_ = lean_ctor_get(v___x_2765_, 3);
lean_inc_ref(v_modules_2766_);
lean_dec_ref(v___x_2765_);
v___x_2767_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2768_ = lean_array_uget_borrowed(v_as_2751_, v_i_2753_);
v___x_2769_ = lean_array_get(v___x_2767_, v_modules_2766_, v_a_2768_);
lean_dec_ref(v_modules_2766_);
v_toImport_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_ref(v_toImport_2770_);
lean_dec(v___x_2769_);
v_module_2771_ = lean_ctor_get(v_toImport_2770_, 0);
lean_inc(v_module_2771_);
lean_dec_ref(v_toImport_2770_);
v___x_2772_ = 0;
lean_inc(v_declName_2750_);
v___x_2773_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2771_, v___x_2772_, v_declName_2750_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; size_t v___x_2775_; size_t v___x_2776_; 
lean_dec_ref_known(v___x_2773_, 1);
v___x_2774_ = lean_box(0);
v___x_2775_ = ((size_t)1ULL);
v___x_2776_ = lean_usize_add(v_i_2753_, v___x_2775_);
v_i_2753_ = v___x_2776_;
v_b_2754_ = v___x_2774_;
goto _start;
}
else
{
lean_dec(v_declName_2750_);
return v___x_2773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2778_, lean_object* v_declName_2779_, lean_object* v_as_2780_, lean_object* v_sz_2781_, lean_object* v_i_2782_, lean_object* v_b_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
size_t v_sz_boxed_2792_; size_t v_i_boxed_2793_; lean_object* v_res_2794_; 
v_sz_boxed_2792_ = lean_unbox_usize(v_sz_2781_);
lean_dec(v_sz_2781_);
v_i_boxed_2793_ = lean_unbox_usize(v_i_2782_);
lean_dec(v_i_2782_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2778_, v_declName_2779_, v_as_2780_, v_sz_boxed_2792_, v_i_boxed_2793_, v_b_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec_ref(v_as_2780_);
lean_dec_ref(v___x_2778_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_a_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2796_) == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_box(0);
return v___x_2797_;
}
else
{
lean_object* v_key_2798_; lean_object* v_value_2799_; lean_object* v_tail_2800_; uint8_t v___x_2801_; 
v_key_2798_ = lean_ctor_get(v_x_2796_, 0);
v_value_2799_ = lean_ctor_get(v_x_2796_, 1);
v_tail_2800_ = lean_ctor_get(v_x_2796_, 2);
v___x_2801_ = lean_name_eq(v_key_2798_, v_a_2795_);
if (v___x_2801_ == 0)
{
v_x_2796_ = v_tail_2800_;
goto _start;
}
else
{
lean_object* v___x_2803_; 
lean_inc(v_value_2799_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_value_2799_);
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_2804_, lean_object* v_x_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2804_, v_x_2805_);
lean_dec(v_x_2805_);
lean_dec(v_a_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_buckets_2809_; lean_object* v___x_2810_; uint64_t v___y_2812_; 
v_buckets_2809_ = lean_ctor_get(v_m_2807_, 1);
v___x_2810_ = lean_array_get_size(v_buckets_2809_);
if (lean_obj_tag(v_a_2808_) == 0)
{
uint64_t v___x_2826_; 
v___x_2826_ = 1723ULL;
v___y_2812_ = v___x_2826_;
goto v___jp_2811_;
}
else
{
uint64_t v_hash_2827_; 
v_hash_2827_ = lean_ctor_get_uint64(v_a_2808_, sizeof(void*)*2);
v___y_2812_ = v_hash_2827_;
goto v___jp_2811_;
}
v___jp_2811_:
{
uint64_t v___x_2813_; uint64_t v___x_2814_; uint64_t v_fold_2815_; uint64_t v___x_2816_; uint64_t v___x_2817_; uint64_t v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2813_ = 32ULL;
v___x_2814_ = lean_uint64_shift_right(v___y_2812_, v___x_2813_);
v_fold_2815_ = lean_uint64_xor(v___y_2812_, v___x_2814_);
v___x_2816_ = 16ULL;
v___x_2817_ = lean_uint64_shift_right(v_fold_2815_, v___x_2816_);
v___x_2818_ = lean_uint64_xor(v_fold_2815_, v___x_2817_);
v___x_2819_ = lean_uint64_to_usize(v___x_2818_);
v___x_2820_ = lean_usize_of_nat(v___x_2810_);
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_sub(v___x_2820_, v___x_2821_);
v___x_2823_ = lean_usize_land(v___x_2819_, v___x_2822_);
v___x_2824_ = lean_array_uget_borrowed(v_buckets_2809_, v___x_2823_);
v___x_2825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2808_, v___x_2824_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2828_, v_a_2829_);
lean_dec(v_a_2829_);
lean_dec_ref(v_m_2828_);
return v_res_2830_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2834_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2835_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2834_, v___x_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2838_, uint8_t v_isMeta_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v_env_2852_; lean_object* v___y_2854_; lean_object* v___x_2867_; 
v___x_2848_ = lean_st_ref_get(v___y_2846_);
v_env_2852_ = lean_ctor_get(v___x_2848_, 0);
lean_inc_ref(v_env_2852_);
lean_dec(v___x_2848_);
v___x_2867_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2852_, v_declName_2838_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec_ref(v_env_2852_);
lean_dec(v_declName_2838_);
goto v___jp_2849_;
}
else
{
lean_object* v_val_2868_; lean_object* v___x_2869_; lean_object* v_modules_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_val_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = l_Lean_Environment_header(v_env_2852_);
v_modules_2870_ = lean_ctor_get(v___x_2869_, 3);
lean_inc_ref(v_modules_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_array_get_size(v_modules_2870_);
v___x_2872_ = lean_nat_dec_lt(v_val_2868_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_dec_ref(v_modules_2870_);
lean_dec(v_val_2868_);
lean_dec_ref(v_env_2852_);
lean_dec(v_declName_2838_);
goto v___jp_2849_;
}
else
{
lean_object* v___x_2873_; lean_object* v_env_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___y_2878_; 
v___x_2873_ = lean_st_ref_get(v___y_2846_);
v_env_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_env_2874_);
lean_dec(v___x_2873_);
v___x_2875_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2876_ = lean_array_fget(v_modules_2870_, v_val_2868_);
lean_dec(v_val_2868_);
lean_dec_ref(v_modules_2870_);
if (v_isMeta_2839_ == 0)
{
lean_dec_ref(v_env_2874_);
v___y_2878_ = v_isMeta_2839_;
goto v___jp_2877_;
}
else
{
uint8_t v___x_2889_; 
lean_inc(v_declName_2838_);
v___x_2889_ = l_Lean_isMarkedMeta(v_env_2874_, v_declName_2838_);
if (v___x_2889_ == 0)
{
v___y_2878_ = v_isMeta_2839_;
goto v___jp_2877_;
}
else
{
uint8_t v___x_2890_; 
v___x_2890_ = 0;
v___y_2878_ = v___x_2890_;
goto v___jp_2877_;
}
}
v___jp_2877_:
{
lean_object* v_toImport_2879_; lean_object* v_module_2880_; lean_object* v___x_2881_; 
v_toImport_2879_ = lean_ctor_get(v___x_2876_, 0);
lean_inc_ref(v_toImport_2879_);
lean_dec(v___x_2876_);
v_module_2880_ = lean_ctor_get(v_toImport_2879_, 0);
lean_inc(v_module_2880_);
lean_dec_ref(v_toImport_2879_);
lean_inc(v_declName_2838_);
v___x_2881_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2880_, v___y_2878_, v_declName_2838_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2881_, 1);
v___x_2882_ = l_Lean_indirectModUseExt;
v___x_2883_ = lean_box(1);
v___x_2884_ = lean_box(0);
lean_inc_ref(v_env_2852_);
v___x_2885_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2875_, v___x_2882_, v_env_2852_, v___x_2883_, v___x_2884_);
v___x_2886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_2885_, v_declName_2838_);
lean_dec(v___x_2885_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2854_ = v___x_2887_;
goto v___jp_2853_;
}
else
{
lean_object* v_val_2888_; 
v_val_2888_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v___x_2886_, 1);
v___y_2854_ = v_val_2888_;
goto v___jp_2853_;
}
}
else
{
lean_dec_ref(v_env_2852_);
lean_dec(v_declName_2838_);
return v___x_2881_;
}
}
}
}
v___jp_2849_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
v___jp_2853_:
{
lean_object* v___x_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = lean_box(0);
v_sz_2856_ = lean_array_size(v___y_2854_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2852_, v_declName_2838_, v___y_2854_, v_sz_2856_, v___x_2857_, v___x_2855_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_env_2852_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; 
v_unused_2866_ = lean_ctor_get(v___x_2858_, 0);
lean_dec(v_unused_2866_);
v___x_2860_ = v___x_2858_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_dec(v___x_2858_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2855_);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2855_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2891_, lean_object* v_isMeta_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v_isMeta_boxed_2901_; lean_object* v_res_2902_; 
v_isMeta_boxed_2901_ = lean_unbox(v_isMeta_2892_);
v_res_2902_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2891_, v_isMeta_boxed_2901_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2903_, lean_object* v_b_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
if (lean_obj_tag(v_as_x27_2903_) == 0)
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_b_2904_);
return v___x_2913_;
}
else
{
lean_object* v_head_2914_; lean_object* v_tail_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; 
v_head_2914_ = lean_ctor_get(v_as_x27_2903_, 0);
v_tail_2915_ = lean_ctor_get(v_as_x27_2903_, 1);
v___x_2916_ = 1;
lean_inc(v_head_2914_);
v___x_2917_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2914_, v___x_2916_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2918_; 
lean_dec_ref_known(v___x_2917_, 1);
v___x_2918_ = lean_box(0);
v_as_x27_2903_ = v_tail_2915_;
v_b_2904_ = v___x_2918_;
goto _start;
}
else
{
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2920_, lean_object* v_b_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2920_, v_b_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v_as_x27_2920_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2931_, lean_object* v_options_2932_, lean_object* v_currNamespace_2933_, lean_object* v_openDecls_2934_, lean_object* v_n_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = l_Lean_ResolveName_resolveGlobalName(v_env_2931_, v_options_2932_, v_currNamespace_2933_, v_openDecls_2934_, v_n_2935_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2940_, lean_object* v_options_2941_, lean_object* v_currNamespace_2942_, lean_object* v_openDecls_2943_, lean_object* v_n_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2940_, v_options_2941_, v_currNamespace_2942_, v_openDecls_2943_, v_n_2944_, v___y_2945_, v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_options_2941_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_2948_, lean_object* v_msg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_toCold_2955_; lean_object* v_currRecDepth_2956_; lean_object* v_ref_2957_; uint8_t v_diag_2958_; uint8_t v_suppressElabErrors_2959_; lean_object* v_ref_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_toCold_2955_ = lean_ctor_get(v___y_2952_, 0);
v_currRecDepth_2956_ = lean_ctor_get(v___y_2952_, 1);
v_ref_2957_ = lean_ctor_get(v___y_2952_, 2);
v_diag_2958_ = lean_ctor_get_uint8(v___y_2952_, sizeof(void*)*3);
v_suppressElabErrors_2959_ = lean_ctor_get_uint8(v___y_2952_, sizeof(void*)*3 + 1);
v_ref_2960_ = l_Lean_replaceRef(v_ref_2948_, v_ref_2957_);
lean_inc(v_currRecDepth_2956_);
lean_inc_ref(v_toCold_2955_);
v___x_2961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2961_, 0, v_toCold_2955_);
lean_ctor_set(v___x_2961_, 1, v_currRecDepth_2956_);
lean_ctor_set(v___x_2961_, 2, v_ref_2960_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*3, v_diag_2958_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*3 + 1, v_suppressElabErrors_2959_);
v___x_2962_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_2949_, v___y_2950_, v___y_2951_, v___x_2961_, v___y_2953_);
lean_dec_ref_known(v___x_2961_, 3);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2963_, lean_object* v_msg_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_2963_, v_msg_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_ref_2963_);
return v_res_2970_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = l_Lean_maxRecDepthErrorMessage;
v___x_2977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_2979_ = l_Lean_MessageData_ofFormat(v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_2981_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_2982_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v___x_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v_ref_2983_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_2988_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v_toCold_3002_; lean_object* v_env_3003_; lean_object* v_currRecDepth_3004_; lean_object* v_ref_3005_; lean_object* v_options_3006_; lean_object* v_maxRecDepth_3007_; lean_object* v_currNamespace_3008_; lean_object* v_openDecls_3009_; lean_object* v_quotContext_3010_; lean_object* v_currMacroScope_3011_; lean_object* v___x_3012_; lean_object* v_nextMacroScope_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___f_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v_methods_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3001_ = lean_st_ref_get(v___y_2999_);
v_toCold_3002_ = lean_ctor_get(v___y_2998_, 0);
v_env_3003_ = lean_ctor_get(v___x_3001_, 0);
lean_inc_ref_n(v_env_3003_, 4);
lean_dec(v___x_3001_);
v_currRecDepth_3004_ = lean_ctor_get(v___y_2998_, 1);
v_ref_3005_ = lean_ctor_get(v___y_2998_, 2);
v_options_3006_ = lean_ctor_get(v_toCold_3002_, 2);
v_maxRecDepth_3007_ = lean_ctor_get(v_toCold_3002_, 3);
v_currNamespace_3008_ = lean_ctor_get(v_toCold_3002_, 4);
v_openDecls_3009_ = lean_ctor_get(v_toCold_3002_, 5);
v_quotContext_3010_ = lean_ctor_get(v_toCold_3002_, 8);
v_currMacroScope_3011_ = lean_ctor_get(v_toCold_3002_, 9);
v___x_3012_ = lean_st_ref_get(v___y_2999_);
v_nextMacroScope_3013_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_nextMacroScope_3013_);
lean_dec(v___x_3012_);
v___f_3014_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3014_, 0, v_env_3003_);
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3015_, 0, v_env_3003_);
lean_inc_n(v_openDecls_3009_, 2);
lean_inc_n(v_currNamespace_3008_, 3);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3016_, 0, v_env_3003_);
lean_closure_set(v___f_3016_, 1, v_currNamespace_3008_);
lean_closure_set(v___f_3016_, 2, v_openDecls_3009_);
v___f_3017_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3017_, 0, v_currNamespace_3008_);
lean_inc_ref(v_options_3006_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3018_, 0, v_env_3003_);
lean_closure_set(v___f_3018_, 1, v_options_3006_);
lean_closure_set(v___f_3018_, 2, v_currNamespace_3008_);
lean_closure_set(v___f_3018_, 3, v_openDecls_3009_);
v_methods_3019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3019_, 0, v___f_3014_);
lean_ctor_set(v_methods_3019_, 1, v___f_3017_);
lean_ctor_set(v_methods_3019_, 2, v___f_3015_);
lean_ctor_set(v_methods_3019_, 3, v___f_3016_);
lean_ctor_set(v_methods_3019_, 4, v___f_3018_);
lean_inc(v_ref_3005_);
lean_inc(v_maxRecDepth_3007_);
lean_inc(v_currRecDepth_3004_);
lean_inc(v_currMacroScope_3011_);
lean_inc(v_quotContext_3010_);
v___x_3020_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3020_, 0, v_methods_3019_);
lean_ctor_set(v___x_3020_, 1, v_quotContext_3010_);
lean_ctor_set(v___x_3020_, 2, v_currMacroScope_3011_);
lean_ctor_set(v___x_3020_, 3, v_currRecDepth_3004_);
lean_ctor_set(v___x_3020_, 4, v_maxRecDepth_3007_);
lean_ctor_set(v___x_3020_, 5, v_ref_3005_);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3022_, 0, v_nextMacroScope_3013_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
v___x_3023_ = lean_apply_2(v_x_2992_, v___x_3020_, v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v_a_3025_; lean_object* v_macroScope_3026_; lean_object* v_traceMsgs_3027_; lean_object* v_expandedMacroDecls_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 1);
lean_inc(v_a_3024_);
v_a_3025_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3023_, 2);
v_macroScope_3026_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_macroScope_3026_);
v_traceMsgs_3027_ = lean_ctor_get(v_a_3024_, 1);
lean_inc(v_traceMsgs_3027_);
v_expandedMacroDecls_3028_ = lean_ctor_get(v_a_3024_, 2);
lean_inc(v_expandedMacroDecls_3028_);
lean_dec(v_a_3024_);
v___x_3029_ = lean_box(0);
v___x_3030_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3028_, v___x_3029_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v_expandedMacroDecls_3028_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v_env_3032_; lean_object* v_ngen_3033_; lean_object* v_auxDeclNGen_3034_; lean_object* v_traceState_3035_; lean_object* v_cache_3036_; lean_object* v_messages_3037_; lean_object* v_infoState_3038_; lean_object* v_snapshotTasks_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref_known(v___x_3030_, 1);
v___x_3031_ = lean_st_ref_take(v___y_2999_);
v_env_3032_ = lean_ctor_get(v___x_3031_, 0);
v_ngen_3033_ = lean_ctor_get(v___x_3031_, 2);
v_auxDeclNGen_3034_ = lean_ctor_get(v___x_3031_, 3);
v_traceState_3035_ = lean_ctor_get(v___x_3031_, 4);
v_cache_3036_ = lean_ctor_get(v___x_3031_, 5);
v_messages_3037_ = lean_ctor_get(v___x_3031_, 6);
v_infoState_3038_ = lean_ctor_get(v___x_3031_, 7);
v_snapshotTasks_3039_ = lean_ctor_get(v___x_3031_, 8);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v___x_3031_, 1);
lean_dec(v_unused_3066_);
v___x_3041_ = v___x_3031_;
v_isShared_3042_ = v_isSharedCheck_3065_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_snapshotTasks_3039_);
lean_inc(v_infoState_3038_);
lean_inc(v_messages_3037_);
lean_inc(v_cache_3036_);
lean_inc(v_traceState_3035_);
lean_inc(v_auxDeclNGen_3034_);
lean_inc(v_ngen_3033_);
lean_inc(v_env_3032_);
lean_dec(v___x_3031_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3065_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 1, v_macroScope_3026_);
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_env_3032_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_macroScope_3026_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_ngen_3033_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_auxDeclNGen_3034_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_traceState_3035_);
lean_ctor_set(v_reuseFailAlloc_3064_, 5, v_cache_3036_);
lean_ctor_set(v_reuseFailAlloc_3064_, 6, v_messages_3037_);
lean_ctor_set(v_reuseFailAlloc_3064_, 7, v_infoState_3038_);
lean_ctor_set(v_reuseFailAlloc_3064_, 8, v_snapshotTasks_3039_);
v___x_3044_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_st_ref_put(v___y_2999_, v___x_3044_);
v___x_3046_ = l_List_reverse___redArg(v_traceMsgs_3027_);
v___x_3047_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3046_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3055_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v_a_3025_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3025_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_a_3025_);
v_a_3056_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3047_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3047_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_traceMsgs_3027_);
lean_dec(v_macroScope_3026_);
lean_dec(v_a_3025_);
v_a_3067_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3030_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3030_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; 
v_a_3075_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3023_, 2);
if (lean_obj_tag(v_a_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v_a_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_a_3076_ = lean_ctor_get(v_a_3075_, 0);
lean_inc(v_a_3076_);
v_a_3077_ = lean_ctor_get(v_a_3075_, 1);
lean_inc_ref(v_a_3077_);
lean_dec_ref_known(v_a_3075_, 2);
v___x_3078_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3079_ = lean_string_dec_eq(v_a_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_a_3077_);
v___x_3081_ = l_Lean_MessageData_ofFormat(v___x_3080_);
v___x_3082_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3076_, v___x_3081_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v_a_3076_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; 
lean_dec_ref(v_a_3077_);
v___x_3083_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3076_);
return v___x_3083_;
}
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec_ref(v___y_3086_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_toCold_3099_; lean_object* v_quotContext_3100_; lean_object* v_currMacroScope_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_toCold_3099_ = lean_ctor_get(v___y_3096_, 0);
lean_inc_ref(v_toCold_3099_);
lean_dec_ref(v___y_3096_);
v_quotContext_3100_ = lean_ctor_get(v_toCold_3099_, 8);
lean_inc(v_quotContext_3100_);
v_currMacroScope_3101_ = lean_ctor_get(v_toCold_3099_, 9);
lean_inc(v_currMacroScope_3101_);
lean_dec_ref(v_toCold_3099_);
v___x_3102_ = l_Lean_addMacroScope(v_quotContext_3100_, v___x_3095_, v_currMacroScope_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___f_3117_; lean_object* v___x_3118_; 
v___f_3117_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3118_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3117_, v___y_3114_, v___y_3115_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3123_, uint8_t v_canonical_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3142_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3142_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = l_Lean_mkIdentFrom(v_ref_3123_, v_a_3134_, v_canonical_3124_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3138_);
v___x_3140_ = v___x_3136_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
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
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3133_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3133_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3151_, lean_object* v_canonical_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v_canonical_boxed_3161_; lean_object* v_res_3162_; 
v_canonical_boxed_3161_ = lean_unbox(v_canonical_3152_);
v_res_3162_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3151_, v_canonical_boxed_3161_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v_ref_3151_);
return v_res_3162_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3175_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3176_ = l_Lean_Name_append(v___x_3175_, v___x_3174_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3179_ = l_Lean_stringToMessageData(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3186_, lean_object* v_letOrReassign_3187_, lean_object* v_decl_3188_, lean_object* v_tk_3189_, lean_object* v_dec_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3186_, v_letOrReassign_3187_, v_decl_3188_, v_tk_3189_, v_dec_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v_a_3191_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3200_, lean_object* v_letOrReassign_3201_, lean_object* v_decl_3202_, lean_object* v_tk_3203_, lean_object* v_dec_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3200_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref_known(v___x_3213_, 1);
lean_inc(v_decl_3202_);
v___x_3214_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3202_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3201_, v_a_3215_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3216_, 1);
v___x_3217_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3204_, v_tk_3203_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3201_, v_decl_3202_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v_doBlockResultType_3221_; lean_object* v___x_3222_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v_doBlockResultType_3221_ = lean_ctor_get(v_a_3205_, 3);
lean_inc_ref(v_doBlockResultType_3221_);
v___x_3222_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3221_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3449_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3449_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3449_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3228_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3230_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3220_);
v___x_3231_ = l_Lean_Syntax_isOfKind(v_a_3220_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; 
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_tk_3203_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v___x_3232_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = l_Lean_Syntax_getArg(v_a_3220_, v___x_3233_);
lean_dec(v_a_3220_);
v___x_3235_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3234_);
v___x_3236_ = l_Lean_Syntax_isOfKind(v___x_3234_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; uint8_t v___x_3238_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v_id_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; 
lean_dec(v_tk_3203_);
v___x_3237_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3234_);
v___x_3238_ = l_Lean_Syntax_isOfKind(v___x_3234_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3352_; uint8_t v___x_3353_; 
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3234_);
v___x_3353_ = l_Lean_Syntax_isOfKind(v___x_3234_, v___x_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; 
lean_dec(v___x_3234_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v___x_3354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3354_;
}
else
{
goto v___jp_3335_;
}
}
else
{
goto v___jp_3335_;
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = l_Lean_Syntax_getArg(v___x_3234_, v___x_3355_);
v___x_3357_ = l_Lean_Syntax_matchesNull(v___x_3356_, v___x_3233_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_dec(v___x_3234_);
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v___x_3358_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v_rhs_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v_xType_x3f_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3359_ = lean_box(v___x_3236_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3360_, 0, v___x_3359_);
v___x_3361_ = l_Lean_Syntax_getArg(v___x_3234_, v___x_3233_);
v___x_3417_ = lean_unsigned_to_nat(2u);
v___x_3418_ = l_Lean_Syntax_getArg(v___x_3234_, v___x_3417_);
v___x_3419_ = l_Lean_Syntax_isNone(v___x_3418_);
if (v___x_3419_ == 0)
{
uint8_t v___x_3420_; 
lean_inc(v___x_3418_);
v___x_3420_ = l_Lean_Syntax_matchesNull(v___x_3418_, v___x_3355_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_dec(v___x_3418_);
lean_dec(v___x_3361_);
lean_dec_ref(v___f_3360_);
lean_dec(v___x_3234_);
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v___x_3421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3233_);
lean_dec(v___x_3418_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3422_);
v___x_3424_ = l_Lean_Syntax_isOfKind(v___x_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_dec(v___x_3422_);
lean_dec(v___x_3361_);
lean_dec_ref(v___f_3360_);
lean_dec(v___x_3234_);
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v___x_3425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3425_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = l_Lean_Syntax_getArg(v___x_3422_, v___x_3355_);
lean_dec(v___x_3422_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 1);
lean_ctor_set(v___x_3225_, 0, v___x_3426_);
v___x_3428_ = v___x_3225_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
v_xType_x3f_3382_ = v___x_3428_;
v___y_3383_ = v_a_3205_;
v___y_3384_ = v_a_3206_;
v___y_3385_ = v_a_3207_;
v___y_3386_ = v_a_3208_;
v___y_3387_ = v_a_3209_;
v___y_3388_ = v_a_3210_;
v___y_3389_ = v_a_3211_;
goto v___jp_3381_;
}
}
}
}
else
{
lean_object* v___x_3430_; 
lean_dec(v___x_3418_);
lean_del_object(v___x_3225_);
v___x_3430_ = lean_box(0);
v_xType_x3f_3382_ = v___x_3430_;
v___y_3383_ = v_a_3205_;
v___y_3384_ = v_a_3206_;
v___y_3385_ = v_a_3207_;
v___y_3386_ = v_a_3208_;
v___y_3387_ = v_a_3209_;
v___y_3388_ = v_a_3210_;
v___y_3389_ = v_a_3211_;
goto v___jp_3381_;
}
v___jp_3362_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___f_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3371_ = lean_box(v___x_3236_);
v___x_3372_ = lean_box(v___x_3231_);
lean_inc(v___x_3361_);
v___f_3373_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3373_, 0, v_rhs_3363_);
lean_closure_set(v___f_3373_, 1, v___x_3371_);
lean_closure_set(v___f_3373_, 2, v_config_3200_);
lean_closure_set(v___f_3373_, 3, v_a_3223_);
lean_closure_set(v___f_3373_, 4, v___x_3372_);
lean_closure_set(v___f_3373_, 5, v___x_3227_);
lean_closure_set(v___f_3373_, 6, v___x_3228_);
lean_closure_set(v___f_3373_, 7, v___x_3229_);
lean_closure_set(v___f_3373_, 8, v___f_3360_);
lean_closure_set(v___f_3373_, 9, v___x_3361_);
v___x_3374_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3374_, 0, v_a_3218_);
v___x_3375_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3375_, 0, v_letOrReassign_3201_);
lean_closure_set(v___x_3375_, 1, v_a_3215_);
lean_closure_set(v___x_3375_, 2, v___x_3374_);
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3377_ = l_Lean_MessageData_ofSyntax(v___x_3361_);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_box(0);
v___x_3380_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3378_, v___x_3375_, v___f_3373_, v___x_3379_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v___x_3380_;
}
v___jp_3381_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_unsigned_to_nat(4u);
v___x_3391_ = l_Lean_Syntax_getArg(v___x_3234_, v___x_3390_);
lean_dec(v___x_3234_);
if (lean_obj_tag(v_xType_x3f_3382_) == 0)
{
v_rhs_3363_ = v___x_3391_;
v___y_3364_ = v___y_3383_;
v___y_3365_ = v___y_3384_;
v___y_3366_ = v___y_3385_;
v___y_3367_ = v___y_3386_;
v___y_3368_ = v___y_3387_;
v___y_3369_ = v___y_3388_;
v___y_3370_ = v___y_3389_;
goto v___jp_3362_;
}
else
{
lean_object* v_toCold_3392_; lean_object* v_val_3393_; lean_object* v_ref_3394_; lean_object* v_quotContext_3395_; lean_object* v_currMacroScope_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_toCold_3392_ = lean_ctor_get(v___y_3388_, 0);
v_val_3393_ = lean_ctor_get(v_xType_x3f_3382_, 0);
lean_inc(v_val_3393_);
lean_dec_ref_known(v_xType_x3f_3382_, 1);
v_ref_3394_ = lean_ctor_get(v___y_3388_, 2);
v_quotContext_3395_ = lean_ctor_get(v_toCold_3392_, 8);
v_currMacroScope_3396_ = lean_ctor_get(v_toCold_3392_, 9);
v___x_3397_ = l_Lean_SourceInfo_fromRef(v_ref_3394_, v___x_3236_);
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3399_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3397_, 7);
v___x_3401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3397_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3403_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3404_ = lean_box(0);
lean_inc(v_currMacroScope_3396_);
lean_inc(v_quotContext_3395_);
v___x_3405_ = l_Lean_addMacroScope(v_quotContext_3395_, v___x_3404_, v_currMacroScope_3396_);
v___x_3406_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3397_);
lean_ctor_set(v___x_3407_, 1, v___x_3403_);
lean_ctor_set(v___x_3407_, 2, v___x_3405_);
lean_ctor_set(v___x_3407_, 3, v___x_3406_);
v___x_3408_ = l_Lean_Syntax_node1(v___x_3397_, v___x_3402_, v___x_3407_);
v___x_3409_ = l_Lean_Syntax_node2(v___x_3397_, v___x_3399_, v___x_3401_, v___x_3408_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3397_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3413_ = l_Lean_Syntax_node1(v___x_3397_, v___x_3412_, v_val_3393_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3397_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = l_Lean_Syntax_node5(v___x_3397_, v___x_3398_, v___x_3409_, v___x_3391_, v___x_3411_, v___x_3413_, v___x_3415_);
v_rhs_3363_ = v___x_3416_;
v___y_3364_ = v___y_3383_;
v___y_3365_ = v___y_3384_;
v___y_3366_ = v___y_3385_;
v___y_3367_ = v___y_3386_;
v___y_3368_ = v___y_3387_;
v___y_3369_ = v___y_3388_;
v___y_3370_ = v___y_3389_;
goto v___jp_3362_;
}
}
}
}
v___jp_3239_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; 
v___x_3256_ = lean_box(v___x_3231_);
v___x_3257_ = lean_box(v___x_3238_);
v___x_3258_ = lean_box(v___y_3255_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3259_, 0, v___y_3245_);
lean_closure_set(v___f_3259_, 1, v___y_3240_);
lean_closure_set(v___f_3259_, 2, v___x_3256_);
lean_closure_set(v___f_3259_, 3, v___x_3257_);
lean_closure_set(v___f_3259_, 4, v___x_3233_);
lean_closure_set(v___f_3259_, 5, v___x_3258_);
v___x_3260_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3252_, v___f_3259_, v___y_3250_, v___y_3251_, v___y_3248_, v___y_3246_, v___y_3249_, v___y_3247_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v_toCold_3262_; lean_object* v_options_3263_; lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3304_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v_toCold_3262_ = lean_ctor_get(v___y_3249_, 0);
v_options_3263_ = lean_ctor_get(v_toCold_3262_, 2);
v_fst_3264_ = lean_ctor_get(v_a_3261_, 0);
v_snd_3265_ = lean_ctor_get(v_a_3261_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_a_3261_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3267_ = v_a_3261_;
v_isShared_3268_ = v_isSharedCheck_3304_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_dec(v_a_3261_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3304_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v_inheritedTraceOptions_3269_; uint8_t v_hasTrace_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v_inheritedTraceOptions_3269_ = lean_ctor_get(v_toCold_3262_, 11);
v_hasTrace_3270_ = lean_ctor_get_uint8(v_options_3263_, sizeof(void*)*1);
v___x_3271_ = lean_box(v___y_3244_);
v___x_3272_ = lean_box(v___y_3241_);
v___x_3273_ = lean_box(v___y_3255_);
v___x_3274_ = lean_box(v___x_3231_);
lean_inc(v_snd_3265_);
v___f_3275_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 19, 10);
lean_closure_set(v___f_3275_, 0, v___y_3243_);
lean_closure_set(v___f_3275_, 1, v___y_3242_);
lean_closure_set(v___f_3275_, 2, v_a_3218_);
lean_closure_set(v___f_3275_, 3, v___x_3271_);
lean_closure_set(v___f_3275_, 4, v___x_3272_);
lean_closure_set(v___f_3275_, 5, v_snd_3265_);
lean_closure_set(v___f_3275_, 6, v___x_3273_);
lean_closure_set(v___f_3275_, 7, v___x_3274_);
lean_closure_set(v___f_3275_, 8, v_letOrReassign_3201_);
lean_closure_set(v___f_3275_, 9, v_a_3215_);
v___x_3276_ = l_Lean_Syntax_getId(v___y_3254_);
lean_dec(v___y_3254_);
v___x_3277_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3276_);
if (v_hasTrace_3270_ == 0)
{
lean_object* v___x_3278_; 
lean_del_object(v___x_3267_);
v___x_3278_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3276_, v_fst_3264_, v_snd_3265_, v___f_3275_, v___y_3255_, v___x_3277_, v___y_3253_, v___y_3250_, v___y_3251_, v___y_3248_, v___y_3246_, v___y_3249_, v___y_3247_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
v___x_3279_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3280_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3281_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3269_, v_options_3263_, v___x_3280_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
lean_del_object(v___x_3267_);
v___x_3282_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3276_, v_fst_3264_, v_snd_3265_, v___f_3275_, v___y_3255_, v___x_3277_, v___y_3253_, v___y_3250_, v___y_3251_, v___y_3248_, v___y_3246_, v___y_3249_, v___y_3247_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
lean_inc(v___x_3276_);
v___x_3283_ = l_Lean_MessageData_ofName(v___x_3276_);
v___x_3284_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 7);
lean_ctor_set(v___x_3267_, 1, v___x_3284_);
lean_ctor_set(v___x_3267_, 0, v___x_3283_);
v___x_3286_ = v___x_3267_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc(v_fst_3264_);
v___x_3287_ = l_Lean_MessageData_ofExpr(v_fst_3264_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
lean_inc(v_snd_3265_);
v___x_3291_ = l_Lean_MessageData_ofExpr(v_snd_3265_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3279_, v___x_3292_, v___y_3248_, v___y_3246_, v___y_3249_, v___y_3247_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref_known(v___x_3293_, 1);
v___x_3294_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3276_, v_fst_3264_, v_snd_3265_, v___f_3275_, v___y_3255_, v___x_3277_, v___y_3253_, v___y_3250_, v___y_3251_, v___y_3248_, v___y_3246_, v___y_3249_, v___y_3247_);
return v___x_3294_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v___x_3276_);
lean_dec_ref(v___f_3275_);
lean_dec(v_snd_3265_);
lean_dec(v_fst_3264_);
v_a_3295_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
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
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v___y_3254_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
v_a_3305_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3260_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3260_);
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
v___jp_3313_:
{
uint8_t v_nondep_3325_; 
v_nondep_3325_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1);
if (v_nondep_3325_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3201_) == 1)
{
uint8_t v_usedOnly_3326_; uint8_t v_zeta_3327_; lean_object* v_eq_x3f_3328_; 
v_usedOnly_3326_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 1);
v_zeta_3327_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 2);
v_eq_x3f_3328_ = lean_ctor_get(v_config_3200_, 0);
lean_inc(v_eq_x3f_3328_);
lean_dec_ref(v_config_3200_);
lean_inc(v_id_3317_);
v___y_3240_ = v___y_3314_;
v___y_3241_ = v_usedOnly_3326_;
v___y_3242_ = v_eq_x3f_3328_;
v___y_3243_ = v_id_3317_;
v___y_3244_ = v_zeta_3327_;
v___y_3245_ = v___y_3316_;
v___y_3246_ = v___y_3322_;
v___y_3247_ = v___y_3324_;
v___y_3248_ = v___y_3321_;
v___y_3249_ = v___y_3323_;
v___y_3250_ = v___y_3319_;
v___y_3251_ = v___y_3320_;
v___y_3252_ = v___y_3315_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v_id_3317_;
v___y_3255_ = v___x_3231_;
goto v___jp_3239_;
}
else
{
uint8_t v_usedOnly_3329_; uint8_t v_zeta_3330_; lean_object* v_eq_x3f_3331_; 
v_usedOnly_3329_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 1);
v_zeta_3330_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 2);
v_eq_x3f_3331_ = lean_ctor_get(v_config_3200_, 0);
lean_inc(v_eq_x3f_3331_);
lean_dec_ref(v_config_3200_);
lean_inc(v_id_3317_);
v___y_3240_ = v___y_3314_;
v___y_3241_ = v_usedOnly_3329_;
v___y_3242_ = v_eq_x3f_3331_;
v___y_3243_ = v_id_3317_;
v___y_3244_ = v_zeta_3330_;
v___y_3245_ = v___y_3316_;
v___y_3246_ = v___y_3322_;
v___y_3247_ = v___y_3324_;
v___y_3248_ = v___y_3321_;
v___y_3249_ = v___y_3323_;
v___y_3250_ = v___y_3319_;
v___y_3251_ = v___y_3320_;
v___y_3252_ = v___y_3315_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v_id_3317_;
v___y_3255_ = v___x_3238_;
goto v___jp_3239_;
}
}
else
{
uint8_t v_usedOnly_3332_; uint8_t v_zeta_3333_; lean_object* v_eq_x3f_3334_; 
v_usedOnly_3332_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 1);
v_zeta_3333_ = lean_ctor_get_uint8(v_config_3200_, sizeof(void*)*1 + 2);
v_eq_x3f_3334_ = lean_ctor_get(v_config_3200_, 0);
lean_inc(v_eq_x3f_3334_);
lean_dec_ref(v_config_3200_);
lean_inc(v_id_3317_);
v___y_3240_ = v___y_3314_;
v___y_3241_ = v_usedOnly_3332_;
v___y_3242_ = v_eq_x3f_3334_;
v___y_3243_ = v_id_3317_;
v___y_3244_ = v_zeta_3333_;
v___y_3245_ = v___y_3316_;
v___y_3246_ = v___y_3322_;
v___y_3247_ = v___y_3324_;
v___y_3248_ = v___y_3321_;
v___y_3249_ = v___y_3323_;
v___y_3250_ = v___y_3319_;
v___y_3251_ = v___y_3320_;
v___y_3252_ = v___y_3315_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v_id_3317_;
v___y_3255_ = v___x_3231_;
goto v___jp_3239_;
}
}
v___jp_3335_:
{
lean_object* v___x_3336_; lean_object* v_id_3337_; lean_object* v_binders_3338_; lean_object* v_type_3339_; lean_object* v_value_3340_; uint8_t v___x_3341_; 
v___x_3336_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3234_);
lean_dec(v___x_3234_);
v_id_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_id_3337_);
v_binders_3338_ = lean_ctor_get(v___x_3336_, 1);
lean_inc_ref(v_binders_3338_);
v_type_3339_ = lean_ctor_get(v___x_3336_, 2);
lean_inc(v_type_3339_);
v_value_3340_ = lean_ctor_get(v___x_3336_, 3);
lean_inc(v_value_3340_);
lean_dec_ref(v___x_3336_);
v___x_3341_ = l_Lean_Syntax_isIdent(v_id_3337_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3337_, v___x_3231_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_id_3337_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___y_3314_ = v_value_3340_;
v___y_3315_ = v_binders_3338_;
v___y_3316_ = v_type_3339_;
v_id_3317_ = v_a_3343_;
v___y_3318_ = v_a_3205_;
v___y_3319_ = v_a_3206_;
v___y_3320_ = v_a_3207_;
v___y_3321_ = v_a_3208_;
v___y_3322_ = v_a_3209_;
v___y_3323_ = v_a_3210_;
v___y_3324_ = v_a_3211_;
goto v___jp_3313_;
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_value_3340_);
lean_dec(v_type_3339_);
lean_dec_ref(v_binders_3338_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3344_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3342_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
v___y_3314_ = v_value_3340_;
v___y_3315_ = v_binders_3338_;
v___y_3316_ = v_type_3339_;
v_id_3317_ = v_id_3337_;
v___y_3318_ = v_a_3205_;
v___y_3319_ = v_a_3206_;
v___y_3320_ = v_a_3207_;
v___y_3321_ = v_a_3208_;
v___y_3322_ = v_a_3209_;
v___y_3323_ = v_a_3210_;
v___y_3324_ = v_a_3211_;
goto v___jp_3313_;
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3215_);
v___x_3431_ = lean_box(v___x_3231_);
lean_inc(v___x_3234_);
v___x_3432_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3432_, 0, v___x_3234_);
lean_closure_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3432_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v_ref_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v_ref_3435_ = lean_ctor_get(v_a_3210_, 2);
v___x_3436_ = 0;
v___x_3437_ = l_Lean_SourceInfo_fromRef(v_ref_3435_, v___x_3436_);
v___x_3438_ = l_Lean_Syntax_node1(v___x_3437_, v___x_3230_, v_a_3434_);
lean_inc(v___x_3438_);
v___x_3439_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3439_, 0, v_config_3200_);
lean_closure_set(v___x_3439_, 1, v_letOrReassign_3201_);
lean_closure_set(v___x_3439_, 2, v___x_3438_);
lean_closure_set(v___x_3439_, 3, v_tk_3203_);
lean_closure_set(v___x_3439_, 4, v_a_3218_);
v___x_3440_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3234_, v___x_3438_, v___x_3439_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
return v___x_3440_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec(v___x_3234_);
lean_dec(v_a_3218_);
lean_dec(v_tk_3203_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3441_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3433_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3433_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3220_);
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_tk_3203_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
return v___x_3222_;
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v_a_3218_);
lean_dec(v_a_3215_);
lean_dec(v_tk_3203_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3450_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3219_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3219_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_a_3215_);
lean_dec(v_tk_3203_);
lean_dec(v_decl_3202_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3458_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3217_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3217_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_a_3215_);
lean_dec_ref(v_dec_3204_);
lean_dec(v_tk_3203_);
lean_dec(v_decl_3202_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3466_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3216_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3216_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v_dec_3204_);
lean_dec(v_tk_3203_);
lean_dec(v_decl_3202_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3474_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3214_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3214_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_dec_3204_);
lean_dec(v_tk_3203_);
lean_dec(v_decl_3202_);
lean_dec(v_letOrReassign_3201_);
lean_dec_ref(v_config_3200_);
v_a_3482_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3213_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3213_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3490_, lean_object* v_x_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3491_, v_x_3492_, v_x_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3495_, lean_object* v_msg_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3495_, v_msg_3496_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3506_, lean_object* v_msg_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3506_, v_msg_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3522_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec_ref(v___y_3526_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3535_, lean_object* v_beforeStx_3536_, lean_object* v_afterStx_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3536_, v_afterStx_3537_, v_x_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3548_, lean_object* v_beforeStx_3549_, lean_object* v_afterStx_3550_, lean_object* v_x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3548_, v_beforeStx_3549_, v_afterStx_3550_, v_x_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3561_, lean_object* v_x_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3562_, v___y_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3566_, v_x_3567_, v___y_3568_, v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_x_3567_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3571_, lean_object* v_ref_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3572_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_ref_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3582_, v_ref_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec_ref(v___y_3584_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3593_, lean_object* v_x_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3604_, v_x_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3615_, lean_object* v_x_3616_, size_t v_x_3617_, size_t v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3616_, v_x_3617_, v_x_3618_, v_x_3619_, v_x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
size_t v_x_89822__boxed_3628_; size_t v_x_89823__boxed_3629_; lean_object* v_res_3630_; 
v_x_89822__boxed_3628_ = lean_unbox_usize(v_x_3624_);
lean_dec(v_x_3624_);
v_x_89823__boxed_3629_ = lean_unbox_usize(v_x_3625_);
lean_dec(v_x_3625_);
v_res_3630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3622_, v_x_3623_, v_x_89822__boxed_3628_, v_x_89823__boxed_3629_, v_x_3626_, v_x_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3631_, lean_object* v_stx_3632_, lean_object* v_output_3633_, lean_object* v_x_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3632_, v_output_3633_, v_x_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_stx_3644_, lean_object* v_output_3645_, lean_object* v_x_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3643_, v_stx_3644_, v_output_3645_, v_x_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3655_, lean_object* v_as_x27_3656_, lean_object* v_b_3657_, lean_object* v_a_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3656_, v_b_3657_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3668_, lean_object* v_as_x27_3669_, lean_object* v_b_3670_, lean_object* v_a_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3668_, v_as_x27_3669_, v_b_3670_, v_a_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v_as_x27_3669_);
lean_dec(v_as_3668_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3681_, lean_object* v_ref_3682_, lean_object* v_msg_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3682_, v_msg_3683_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_ref_3694_, lean_object* v_msg_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3693_, v_ref_3694_, v_msg_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v_ref_3694_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3705_, lean_object* v_n_3706_, lean_object* v_k_3707_, lean_object* v_v_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3706_, v_k_3707_, v_v_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3710_, size_t v_depth_3711_, lean_object* v_keys_3712_, lean_object* v_vals_3713_, lean_object* v_heq_3714_, lean_object* v_i_3715_, lean_object* v_entries_3716_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3711_, v_keys_3712_, v_vals_3713_, v_i_3715_, v_entries_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3718_, lean_object* v_depth_3719_, lean_object* v_keys_3720_, lean_object* v_vals_3721_, lean_object* v_heq_3722_, lean_object* v_i_3723_, lean_object* v_entries_3724_){
_start:
{
size_t v_depth_boxed_3725_; lean_object* v_res_3726_; 
v_depth_boxed_3725_ = lean_unbox_usize(v_depth_3719_);
lean_dec(v_depth_3719_);
v_res_3726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3718_, v_depth_boxed_3725_, v_keys_3720_, v_vals_3721_, v_heq_3722_, v_i_3723_, v_entries_3724_);
lean_dec_ref(v_vals_3721_);
lean_dec_ref(v_keys_3720_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3732_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3743_, lean_object* v_x_3744_, lean_object* v_mkInfoTree_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3744_, v_mkInfoTree_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3754_, lean_object* v_x_3755_, lean_object* v_mkInfoTree_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3754_, v_x_3755_, v_mkInfoTree_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3765_, lean_object* v_m_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3766_, v_a_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3769_, lean_object* v_m_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3769_, v_m_3770_, v_a_3771_);
lean_dec(v_a_3771_);
lean_dec_ref(v_m_3770_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3774_, v_x_3775_, v_x_3776_, v_x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3779_, lean_object* v_x_3780_, lean_object* v_x_3781_){
_start:
{
uint8_t v___x_3782_; 
v___x_3782_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3780_, v_x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
uint8_t v_res_3786_; lean_object* v_r_3787_; 
v_res_3786_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3783_, v_x_3784_, v_x_3785_);
lean_dec_ref(v_x_3785_);
lean_dec_ref(v_x_3784_);
v_r_3787_ = lean_box(v_res_3786_);
return v_r_3787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3788_, lean_object* v_a_3789_, lean_object* v_x_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_3789_, v_x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3792_, lean_object* v_a_3793_, lean_object* v_x_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3792_, v_a_3793_, v_x_3794_);
lean_dec(v_x_3794_);
lean_dec(v_a_3793_);
return v_res_3795_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3796_, lean_object* v_x_3797_, size_t v_x_3798_, lean_object* v_x_3799_){
_start:
{
uint8_t v___x_3800_; 
v___x_3800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3797_, v_x_3798_, v_x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3801_, lean_object* v_x_3802_, lean_object* v_x_3803_, lean_object* v_x_3804_){
_start:
{
size_t v_x_89992__boxed_3805_; uint8_t v_res_3806_; lean_object* v_r_3807_; 
v_x_89992__boxed_3805_ = lean_unbox_usize(v_x_3803_);
lean_dec(v_x_3803_);
v_res_3806_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3801_, v_x_3802_, v_x_89992__boxed_3805_, v_x_3804_);
lean_dec_ref(v_x_3804_);
lean_dec_ref(v_x_3802_);
v_r_3807_ = lean_box(v_res_3806_);
return v_r_3807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3808_, lean_object* v_keys_3809_, lean_object* v_vals_3810_, lean_object* v_heq_3811_, lean_object* v_i_3812_, lean_object* v_k_3813_){
_start:
{
uint8_t v___x_3814_; 
v___x_3814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3809_, v_i_3812_, v_k_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3815_, lean_object* v_keys_3816_, lean_object* v_vals_3817_, lean_object* v_heq_3818_, lean_object* v_i_3819_, lean_object* v_k_3820_){
_start:
{
uint8_t v_res_3821_; lean_object* v_r_3822_; 
v_res_3821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3815_, v_keys_3816_, v_vals_3817_, v_heq_3818_, v_i_3819_, v_k_3820_);
lean_dec_ref(v_k_3820_);
lean_dec_ref(v_vals_3817_);
lean_dec_ref(v_keys_3816_);
v_r_3822_ = lean_box(v_res_3821_);
return v_r_3822_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3826_ = l_Lean_stringToMessageData(v___x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3832_, lean_object* v_otherwise_x3f_3833_, uint8_t v___x_3834_, lean_object* v___x_3835_, lean_object* v___x_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v_dec_3840_, uint8_t v___x_3841_, lean_object* v___y_3842_, lean_object* v___x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; uint8_t v___y_3875_; 
switch(lean_obj_tag(v_letOrReassign_3832_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3833_) == 1)
{
lean_object* v_mutTk_x3f_3886_; lean_object* v_val_3887_; lean_object* v_ref_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3918_; 
v_mutTk_x3f_3886_ = lean_ctor_get(v_letOrReassign_3832_, 0);
v_val_3887_ = lean_ctor_get(v_otherwise_x3f_3833_, 0);
lean_inc(v_val_3887_);
lean_dec_ref_known(v_otherwise_x3f_3833_, 1);
v_ref_3888_ = lean_ctor_get(v___y_3849_, 2);
v___x_3889_ = l_Lean_SourceInfo_fromRef(v_ref_3888_, v___x_3834_);
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3837_);
lean_inc_ref(v___x_3836_);
lean_inc_ref(v___x_3835_);
v___x_3891_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3890_);
v___x_3892_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3889_);
v___x_3893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3889_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3895_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3886_) == 1)
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_val_3933_ = lean_ctor_get(v_mutTk_x3f_3886_, 0);
v___x_3934_ = l_Lean_SourceInfo_fromRef(v_val_3933_, v___x_3841_);
v___x_3935_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Array_mkArray1___redArg(v___x_3936_);
v___y_3918_ = v___x_3937_;
goto v___jp_3917_;
}
else
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_mk_empty_array_with_capacity(v___x_3843_);
v___y_3918_ = v___x_3938_;
goto v___jp_3917_;
}
v___jp_3896_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3902_ = l_Array_append___redArg(v___x_3895_, v___y_3901_);
lean_dec_ref(v___y_3901_);
lean_inc(v___x_3889_);
v___x_3903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3889_);
lean_ctor_set(v___x_3903_, 1, v___x_3894_);
lean_ctor_set(v___x_3903_, 2, v___x_3902_);
v___x_3904_ = lean_unsigned_to_nat(9u);
v___x_3905_ = lean_mk_empty_array_with_capacity(v___x_3904_);
v___x_3906_ = lean_array_push(v___x_3905_, v___x_3893_);
v___x_3907_ = lean_array_push(v___x_3906_, v___y_3899_);
v___x_3908_ = lean_array_push(v___x_3907_, v___y_3897_);
v___x_3909_ = lean_array_push(v___x_3908_, v___x_3838_);
v___x_3910_ = lean_array_push(v___x_3909_, v___y_3900_);
v___x_3911_ = lean_array_push(v___x_3910_, v___x_3839_);
v___x_3912_ = lean_array_push(v___x_3911_, v___y_3898_);
v___x_3913_ = lean_array_push(v___x_3912_, v_val_3887_);
v___x_3914_ = lean_array_push(v___x_3913_, v___x_3903_);
v___x_3915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3889_);
lean_ctor_set(v___x_3915_, 1, v___x_3891_);
lean_ctor_set(v___x_3915_, 2, v___x_3914_);
v___x_3916_ = l_Lean_Elab_Do_elabDoElem(v___x_3915_, v_dec_3840_, v___x_3841_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3916_;
}
v___jp_3917_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3919_ = l_Array_append___redArg(v___x_3895_, v___y_3918_);
lean_dec_ref(v___y_3918_);
lean_inc_n(v___x_3889_, 5);
v___x_3920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3889_);
lean_ctor_set(v___x_3920_, 1, v___x_3894_);
lean_ctor_set(v___x_3920_, 2, v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3922_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3921_);
v___x_3923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3889_);
lean_ctor_set(v___x_3923_, 1, v___x_3894_);
lean_ctor_set(v___x_3923_, 2, v___x_3895_);
v___x_3924_ = l_Lean_Syntax_node1(v___x_3889_, v___x_3922_, v___x_3923_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3889_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_3928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3889_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
if (lean_obj_tag(v___y_3842_) == 0)
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_mk_empty_array_with_capacity(v___x_3843_);
v___y_3897_ = v___x_3924_;
v___y_3898_ = v___x_3928_;
v___y_3899_ = v___x_3920_;
v___y_3900_ = v___x_3926_;
v___y_3901_ = v___x_3929_;
goto v___jp_3896_;
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_val_3930_ = lean_ctor_get(v___y_3842_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v___y_3842_, 1);
v___x_3931_ = lean_mk_empty_array_with_capacity(v___x_3843_);
v___x_3932_ = lean_array_push(v___x_3931_, v_val_3930_);
v___y_3897_ = v___x_3924_;
v___y_3898_ = v___x_3928_;
v___y_3899_ = v___x_3920_;
v___y_3900_ = v___x_3926_;
v___y_3901_ = v___x_3932_;
goto v___jp_3896_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3939_; lean_object* v_ref_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___y_3949_; 
lean_dec(v___y_3842_);
lean_dec(v_otherwise_x3f_3833_);
v_mutTk_x3f_3939_ = lean_ctor_get(v_letOrReassign_3832_, 0);
v_ref_3940_ = lean_ctor_get(v___y_3849_, 2);
v___x_3941_ = l_Lean_SourceInfo_fromRef(v_ref_3940_, v___x_3834_);
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3837_);
lean_inc_ref(v___x_3836_);
lean_inc_ref(v___x_3835_);
v___x_3943_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3942_);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3941_);
v___x_3945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3941_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3947_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3939_) == 1)
{
lean_object* v_val_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_val_3966_ = lean_ctor_get(v_mutTk_x3f_3939_, 0);
v___x_3967_ = l_Lean_SourceInfo_fromRef(v_val_3966_, v___x_3841_);
v___x_3968_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Array_mkArray1___redArg(v___x_3969_);
v___y_3949_ = v___x_3970_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_mk_empty_array_with_capacity(v___x_3843_);
v___y_3949_ = v___x_3971_;
goto v___jp_3948_;
}
v___jp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3950_ = l_Array_append___redArg(v___x_3947_, v___y_3949_);
lean_dec_ref(v___y_3949_);
lean_inc_n(v___x_3941_, 6);
v___x_3951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3941_);
lean_ctor_set(v___x_3951_, 1, v___x_3946_);
lean_ctor_set(v___x_3951_, 2, v___x_3950_);
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3837_, 2);
lean_inc_ref_n(v___x_3836_, 2);
lean_inc_ref_n(v___x_3835_, 2);
v___x_3953_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3941_);
lean_ctor_set(v___x_3954_, 1, v___x_3946_);
lean_ctor_set(v___x_3954_, 2, v___x_3947_);
lean_inc_ref_n(v___x_3954_, 2);
v___x_3955_ = l_Lean_Syntax_node1(v___x_3941_, v___x_3953_, v___x_3954_);
v___x_3956_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3957_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3956_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3959_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3941_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_Syntax_node5(v___x_3941_, v___x_3959_, v___x_3838_, v___x_3954_, v___x_3954_, v___x_3961_, v___x_3839_);
v___x_3963_ = l_Lean_Syntax_node1(v___x_3941_, v___x_3957_, v___x_3962_);
v___x_3964_ = l_Lean_Syntax_node4(v___x_3941_, v___x_3943_, v___x_3945_, v___x_3951_, v___x_3955_, v___x_3963_);
v___x_3965_ = l_Lean_Elab_Do_elabDoElem(v___x_3964_, v_dec_3840_, v___x_3841_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3965_;
}
}
}
case 1:
{
lean_dec(v___y_3842_);
if (lean_obj_tag(v_otherwise_x3f_3833_) == 1)
{
lean_object* v___x_3972_; 
lean_dec_ref_known(v_otherwise_x3f_3833_, 1);
lean_dec_ref(v_dec_3840_);
lean_dec(v___x_3839_);
lean_dec(v___x_3838_);
lean_dec_ref(v___x_3837_);
lean_dec_ref(v___x_3836_);
lean_dec_ref(v___x_3835_);
v___x_3972_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3972_;
}
else
{
lean_object* v_ref_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_otherwise_x3f_3833_);
v_ref_3973_ = lean_ctor_get(v___y_3849_, 2);
v___x_3974_ = l_Lean_SourceInfo_fromRef(v_ref_3973_, v___x_3834_);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3837_, 3);
lean_inc_ref_n(v___x_3836_, 3);
lean_inc_ref_n(v___x_3835_, 3);
v___x_3976_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3975_);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3974_, 6);
v___x_3978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3974_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3980_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3979_);
v___x_3981_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3982_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3974_);
lean_ctor_set(v___x_3983_, 1, v___x_3981_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
lean_inc_ref_n(v___x_3983_, 2);
v___x_3984_ = l_Lean_Syntax_node1(v___x_3974_, v___x_3980_, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3986_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3985_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3988_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3987_);
v___x_3989_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3974_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = l_Lean_Syntax_node5(v___x_3974_, v___x_3988_, v___x_3838_, v___x_3983_, v___x_3983_, v___x_3990_, v___x_3839_);
v___x_3992_ = l_Lean_Syntax_node1(v___x_3974_, v___x_3986_, v___x_3991_);
v___x_3993_ = l_Lean_Syntax_node3(v___x_3974_, v___x_3976_, v___x_3978_, v___x_3984_, v___x_3992_);
v___x_3994_ = l_Lean_Elab_Do_elabDoElem(v___x_3993_, v_dec_3840_, v___x_3841_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3994_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3833_);
if (lean_obj_tag(v___y_3842_) == 0)
{
v___y_3875_ = v___x_3841_;
goto v___jp_3874_;
}
else
{
lean_dec_ref_known(v___y_3842_, 1);
v___y_3875_ = v___x_3834_;
goto v___jp_3874_;
}
}
}
v___jp_3852_:
{
lean_object* v_ref_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_ref_3860_ = lean_ctor_get(v___y_3858_, 2);
v___x_3861_ = l_Lean_SourceInfo_fromRef(v_ref_3860_, v___x_3834_);
v___x_3862_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3837_);
lean_inc_ref(v___x_3836_);
lean_inc_ref(v___x_3835_);
v___x_3863_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3862_);
v___x_3864_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3865_ = l_Lean_Name_mkStr4(v___x_3835_, v___x_3836_, v___x_3837_, v___x_3864_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3867_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3861_, 3);
v___x_3868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3861_);
lean_ctor_set(v___x_3868_, 1, v___x_3866_);
lean_ctor_set(v___x_3868_, 2, v___x_3867_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3861_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
lean_inc_ref(v___x_3868_);
v___x_3871_ = l_Lean_Syntax_node5(v___x_3861_, v___x_3865_, v___x_3838_, v___x_3868_, v___x_3868_, v___x_3870_, v___x_3839_);
v___x_3872_ = l_Lean_Syntax_node1(v___x_3861_, v___x_3863_, v___x_3871_);
v___x_3873_ = l_Lean_Elab_Do_elabDoElem(v___x_3872_, v_dec_3840_, v___x_3841_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3873_;
}
v___jp_3874_:
{
if (v___y_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_dec_3840_);
lean_dec(v___x_3839_);
lean_dec(v___x_3838_);
lean_dec_ref(v___x_3837_);
lean_dec_ref(v___x_3836_);
lean_dec_ref(v___x_3835_);
v___x_3876_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3877_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_3876_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
else
{
v___y_3853_ = v___y_3844_;
v___y_3854_ = v___y_3845_;
v___y_3855_ = v___y_3846_;
v___y_3856_ = v___y_3847_;
v___y_3857_ = v___y_3848_;
v___y_3858_ = v___y_3849_;
v___y_3859_ = v___y_3850_;
goto v___jp_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_3995_ = _args[0];
lean_object* v_otherwise_x3f_3996_ = _args[1];
lean_object* v___x_3997_ = _args[2];
lean_object* v___x_3998_ = _args[3];
lean_object* v___x_3999_ = _args[4];
lean_object* v___x_4000_ = _args[5];
lean_object* v___x_4001_ = _args[6];
lean_object* v___x_4002_ = _args[7];
lean_object* v_dec_4003_ = _args[8];
lean_object* v___x_4004_ = _args[9];
lean_object* v___y_4005_ = _args[10];
lean_object* v___x_4006_ = _args[11];
lean_object* v___y_4007_ = _args[12];
lean_object* v___y_4008_ = _args[13];
lean_object* v___y_4009_ = _args[14];
lean_object* v___y_4010_ = _args[15];
lean_object* v___y_4011_ = _args[16];
lean_object* v___y_4012_ = _args[17];
lean_object* v___y_4013_ = _args[18];
lean_object* v___y_4014_ = _args[19];
_start:
{
uint8_t v___x_30492__boxed_4015_; uint8_t v___x_30498__boxed_4016_; lean_object* v_res_4017_; 
v___x_30492__boxed_4015_ = lean_unbox(v___x_3997_);
v___x_30498__boxed_4016_ = lean_unbox(v___x_4004_);
v_res_4017_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_3995_, v_otherwise_x3f_3996_, v___x_30492__boxed_4015_, v___x_3998_, v___x_3999_, v___x_4000_, v___x_4001_, v___x_4002_, v_dec_4003_, v___x_30498__boxed_4016_, v___y_4005_, v___x_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___x_4006_);
lean_dec(v_letOrReassign_3995_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4018_, lean_object* v_otherwise_x3f_4019_, uint8_t v___x_4020_, lean_object* v___x_4021_, lean_object* v___x_4022_, lean_object* v___x_4023_, lean_object* v___x_4024_, lean_object* v___x_4025_, lean_object* v_dec_4026_, uint8_t v___x_4027_, lean_object* v___y_4028_, lean_object* v___x_4029_, uint8_t v___x_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4062_; 
switch(lean_obj_tag(v_letOrReassign_4018_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4019_) == 1)
{
lean_object* v_mutTk_x3f_4073_; lean_object* v_val_4074_; lean_object* v_ref_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4105_; 
v_mutTk_x3f_4073_ = lean_ctor_get(v_letOrReassign_4018_, 0);
v_val_4074_ = lean_ctor_get(v_otherwise_x3f_4019_, 0);
lean_inc(v_val_4074_);
lean_dec_ref_known(v_otherwise_x3f_4019_, 1);
v_ref_4075_ = lean_ctor_get(v___y_4036_, 2);
v___x_4076_ = l_Lean_SourceInfo_fromRef(v_ref_4075_, v___x_4020_);
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4023_);
lean_inc_ref(v___x_4022_);
lean_inc_ref(v___x_4021_);
v___x_4078_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4077_);
v___x_4079_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4076_);
v___x_4080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4076_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4082_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4073_) == 1)
{
lean_object* v_val_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_val_4120_ = lean_ctor_get(v_mutTk_x3f_4073_, 0);
v___x_4121_ = l_Lean_SourceInfo_fromRef(v_val_4120_, v___x_4027_);
v___x_4122_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Array_mkArray1___redArg(v___x_4123_);
v___y_4105_ = v___x_4124_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_mk_empty_array_with_capacity(v___x_4029_);
v___y_4105_ = v___x_4125_;
goto v___jp_4104_;
}
v___jp_4083_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4089_ = l_Array_append___redArg(v___x_4082_, v___y_4088_);
lean_dec_ref(v___y_4088_);
lean_inc(v___x_4076_);
v___x_4090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4076_);
lean_ctor_set(v___x_4090_, 1, v___x_4081_);
lean_ctor_set(v___x_4090_, 2, v___x_4089_);
v___x_4091_ = lean_unsigned_to_nat(9u);
v___x_4092_ = lean_mk_empty_array_with_capacity(v___x_4091_);
v___x_4093_ = lean_array_push(v___x_4092_, v___x_4080_);
v___x_4094_ = lean_array_push(v___x_4093_, v___y_4086_);
v___x_4095_ = lean_array_push(v___x_4094_, v___y_4084_);
v___x_4096_ = lean_array_push(v___x_4095_, v___x_4024_);
v___x_4097_ = lean_array_push(v___x_4096_, v___y_4087_);
v___x_4098_ = lean_array_push(v___x_4097_, v___x_4025_);
v___x_4099_ = lean_array_push(v___x_4098_, v___y_4085_);
v___x_4100_ = lean_array_push(v___x_4099_, v_val_4074_);
v___x_4101_ = lean_array_push(v___x_4100_, v___x_4090_);
v___x_4102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4076_);
lean_ctor_set(v___x_4102_, 1, v___x_4078_);
lean_ctor_set(v___x_4102_, 2, v___x_4101_);
v___x_4103_ = l_Lean_Elab_Do_elabDoElem(v___x_4102_, v_dec_4026_, v___x_4027_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4103_;
}
v___jp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4106_ = l_Array_append___redArg(v___x_4082_, v___y_4105_);
lean_dec_ref(v___y_4105_);
lean_inc_n(v___x_4076_, 5);
v___x_4107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4076_);
lean_ctor_set(v___x_4107_, 1, v___x_4081_);
lean_ctor_set(v___x_4107_, 2, v___x_4106_);
v___x_4108_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4109_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4108_);
v___x_4110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4076_);
lean_ctor_set(v___x_4110_, 1, v___x_4081_);
lean_ctor_set(v___x_4110_, 2, v___x_4082_);
v___x_4111_ = l_Lean_Syntax_node1(v___x_4076_, v___x_4109_, v___x_4110_);
v___x_4112_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4076_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4076_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
if (lean_obj_tag(v___y_4028_) == 0)
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_mk_empty_array_with_capacity(v___x_4029_);
v___y_4084_ = v___x_4111_;
v___y_4085_ = v___x_4115_;
v___y_4086_ = v___x_4107_;
v___y_4087_ = v___x_4113_;
v___y_4088_ = v___x_4116_;
goto v___jp_4083_;
}
else
{
lean_object* v_val_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_val_4117_ = lean_ctor_get(v___y_4028_, 0);
lean_inc(v_val_4117_);
lean_dec_ref_known(v___y_4028_, 1);
v___x_4118_ = lean_mk_empty_array_with_capacity(v___x_4029_);
v___x_4119_ = lean_array_push(v___x_4118_, v_val_4117_);
v___y_4084_ = v___x_4111_;
v___y_4085_ = v___x_4115_;
v___y_4086_ = v___x_4107_;
v___y_4087_ = v___x_4113_;
v___y_4088_ = v___x_4119_;
goto v___jp_4083_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4126_; lean_object* v_ref_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___y_4136_; 
lean_dec(v___y_4028_);
lean_dec(v_otherwise_x3f_4019_);
v_mutTk_x3f_4126_ = lean_ctor_get(v_letOrReassign_4018_, 0);
v_ref_4127_ = lean_ctor_get(v___y_4036_, 2);
v___x_4128_ = l_Lean_SourceInfo_fromRef(v_ref_4127_, v___x_4020_);
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4023_);
lean_inc_ref(v___x_4022_);
lean_inc_ref(v___x_4021_);
v___x_4130_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4129_);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4128_);
v___x_4132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4128_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4134_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4126_) == 1)
{
lean_object* v_val_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_val_4153_ = lean_ctor_get(v_mutTk_x3f_4126_, 0);
v___x_4154_ = l_Lean_SourceInfo_fromRef(v_val_4153_, v___x_4027_);
v___x_4155_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Array_mkArray1___redArg(v___x_4156_);
v___y_4136_ = v___x_4157_;
goto v___jp_4135_;
}
else
{
lean_object* v___x_4158_; 
v___x_4158_ = lean_mk_empty_array_with_capacity(v___x_4029_);
v___y_4136_ = v___x_4158_;
goto v___jp_4135_;
}
v___jp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4137_ = l_Array_append___redArg(v___x_4134_, v___y_4136_);
lean_dec_ref(v___y_4136_);
lean_inc_n(v___x_4128_, 6);
v___x_4138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4128_);
lean_ctor_set(v___x_4138_, 1, v___x_4133_);
lean_ctor_set(v___x_4138_, 2, v___x_4137_);
v___x_4139_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4023_, 2);
lean_inc_ref_n(v___x_4022_, 2);
lean_inc_ref_n(v___x_4021_, 2);
v___x_4140_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4128_);
lean_ctor_set(v___x_4141_, 1, v___x_4133_);
lean_ctor_set(v___x_4141_, 2, v___x_4134_);
lean_inc_ref_n(v___x_4141_, 2);
v___x_4142_ = l_Lean_Syntax_node1(v___x_4128_, v___x_4140_, v___x_4141_);
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4144_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4143_);
v___x_4145_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4146_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4145_);
v___x_4147_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4128_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_Syntax_node5(v___x_4128_, v___x_4146_, v___x_4024_, v___x_4141_, v___x_4141_, v___x_4148_, v___x_4025_);
v___x_4150_ = l_Lean_Syntax_node1(v___x_4128_, v___x_4144_, v___x_4149_);
v___x_4151_ = l_Lean_Syntax_node4(v___x_4128_, v___x_4130_, v___x_4132_, v___x_4138_, v___x_4142_, v___x_4150_);
v___x_4152_ = l_Lean_Elab_Do_elabDoElem(v___x_4151_, v_dec_4026_, v___x_4027_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4152_;
}
}
}
case 1:
{
lean_dec(v___y_4028_);
if (lean_obj_tag(v_otherwise_x3f_4019_) == 1)
{
lean_object* v___x_4159_; 
lean_dec_ref_known(v_otherwise_x3f_4019_, 1);
lean_dec_ref(v_dec_4026_);
lean_dec(v___x_4025_);
lean_dec(v___x_4024_);
lean_dec_ref(v___x_4023_);
lean_dec_ref(v___x_4022_);
lean_dec_ref(v___x_4021_);
v___x_4159_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4159_;
}
else
{
lean_object* v_ref_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_dec(v_otherwise_x3f_4019_);
v_ref_4160_ = lean_ctor_get(v___y_4036_, 2);
v___x_4161_ = l_Lean_SourceInfo_fromRef(v_ref_4160_, v___x_4020_);
v___x_4162_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4023_, 3);
lean_inc_ref_n(v___x_4022_, 3);
lean_inc_ref_n(v___x_4021_, 3);
v___x_4163_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4162_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4161_, 6);
v___x_4165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4161_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4167_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4166_);
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4169_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4161_);
lean_ctor_set(v___x_4170_, 1, v___x_4168_);
lean_ctor_set(v___x_4170_, 2, v___x_4169_);
lean_inc_ref_n(v___x_4170_, 2);
v___x_4171_ = l_Lean_Syntax_node1(v___x_4161_, v___x_4167_, v___x_4170_);
v___x_4172_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4173_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4172_);
v___x_4174_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4175_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4174_);
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4161_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_Syntax_node5(v___x_4161_, v___x_4175_, v___x_4024_, v___x_4170_, v___x_4170_, v___x_4177_, v___x_4025_);
v___x_4179_ = l_Lean_Syntax_node1(v___x_4161_, v___x_4173_, v___x_4178_);
v___x_4180_ = l_Lean_Syntax_node3(v___x_4161_, v___x_4163_, v___x_4165_, v___x_4171_, v___x_4179_);
v___x_4181_ = l_Lean_Elab_Do_elabDoElem(v___x_4180_, v_dec_4026_, v___x_4027_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4181_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4019_);
if (lean_obj_tag(v___y_4028_) == 0)
{
v___y_4062_ = v___x_4030_;
goto v___jp_4061_;
}
else
{
lean_dec_ref_known(v___y_4028_, 1);
v___y_4062_ = v___x_4020_;
goto v___jp_4061_;
}
}
}
v___jp_4039_:
{
lean_object* v_ref_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_ref_4047_ = lean_ctor_get(v___y_4045_, 2);
v___x_4048_ = l_Lean_SourceInfo_fromRef(v_ref_4047_, v___x_4020_);
v___x_4049_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4023_);
lean_inc_ref(v___x_4022_);
lean_inc_ref(v___x_4021_);
v___x_4050_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4049_);
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4052_ = l_Lean_Name_mkStr4(v___x_4021_, v___x_4022_, v___x_4023_, v___x_4051_);
v___x_4053_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4054_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4048_, 3);
v___x_4055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4048_);
lean_ctor_set(v___x_4055_, 1, v___x_4053_);
lean_ctor_set(v___x_4055_, 2, v___x_4054_);
v___x_4056_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4048_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
lean_inc_ref(v___x_4055_);
v___x_4058_ = l_Lean_Syntax_node5(v___x_4048_, v___x_4052_, v___x_4024_, v___x_4055_, v___x_4055_, v___x_4057_, v___x_4025_);
v___x_4059_ = l_Lean_Syntax_node1(v___x_4048_, v___x_4050_, v___x_4058_);
v___x_4060_ = l_Lean_Elab_Do_elabDoElem(v___x_4059_, v_dec_4026_, v___x_4027_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4060_;
}
v___jp_4061_:
{
if (v___y_4062_ == 0)
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v_dec_4026_);
lean_dec(v___x_4025_);
lean_dec(v___x_4024_);
lean_dec_ref(v___x_4023_);
lean_dec_ref(v___x_4022_);
lean_dec_ref(v___x_4021_);
v___x_4063_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4064_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4063_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
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
else
{
v___y_4040_ = v___y_4031_;
v___y_4041_ = v___y_4032_;
v___y_4042_ = v___y_4033_;
v___y_4043_ = v___y_4034_;
v___y_4044_ = v___y_4035_;
v___y_4045_ = v___y_4036_;
v___y_4046_ = v___y_4037_;
goto v___jp_4039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4182_ = _args[0];
lean_object* v_otherwise_x3f_4183_ = _args[1];
lean_object* v___x_4184_ = _args[2];
lean_object* v___x_4185_ = _args[3];
lean_object* v___x_4186_ = _args[4];
lean_object* v___x_4187_ = _args[5];
lean_object* v___x_4188_ = _args[6];
lean_object* v___x_4189_ = _args[7];
lean_object* v_dec_4190_ = _args[8];
lean_object* v___x_4191_ = _args[9];
lean_object* v___y_4192_ = _args[10];
lean_object* v___x_4193_ = _args[11];
lean_object* v___x_4194_ = _args[12];
lean_object* v___y_4195_ = _args[13];
lean_object* v___y_4196_ = _args[14];
lean_object* v___y_4197_ = _args[15];
lean_object* v___y_4198_ = _args[16];
lean_object* v___y_4199_ = _args[17];
lean_object* v___y_4200_ = _args[18];
lean_object* v___y_4201_ = _args[19];
lean_object* v___y_4202_ = _args[20];
_start:
{
uint8_t v___x_30874__boxed_4203_; uint8_t v___x_30880__boxed_4204_; uint8_t v___x_30883__boxed_4205_; lean_object* v_res_4206_; 
v___x_30874__boxed_4203_ = lean_unbox(v___x_4184_);
v___x_30880__boxed_4204_ = lean_unbox(v___x_4191_);
v___x_30883__boxed_4205_ = lean_unbox(v___x_4194_);
v_res_4206_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4182_, v_otherwise_x3f_4183_, v___x_30874__boxed_4203_, v___x_4185_, v___x_4186_, v___x_4187_, v___x_4188_, v___x_4189_, v_dec_4190_, v___x_30880__boxed_4204_, v___y_4192_, v___x_4193_, v___x_30883__boxed_4205_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___x_4193_);
lean_dec(v_letOrReassign_4182_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4227_, lean_object* v_stx_4228_, lean_object* v_tk_4229_, lean_object* v_dec_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4239_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4240_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4242_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4228_);
v___x_4243_ = l_Lean_Syntax_isOfKind(v_stx_4228_, v___x_4242_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4244_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4228_);
v___x_4245_ = l_Lean_Syntax_isOfKind(v_stx_4228_, v___x_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4246_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4246_;
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; 
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4247_);
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4248_);
v___x_4250_ = l_Lean_Syntax_isOfKind(v___x_4248_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4336_; lean_object* v_patType_x3f_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4336_ = lean_unsigned_to_nat(1u);
v___x_4367_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4336_);
v___x_4368_ = l_Lean_Syntax_isNone(v___x_4367_);
if (v___x_4368_ == 0)
{
uint8_t v___x_4369_; 
lean_inc(v___x_4367_);
v___x_4369_ = l_Lean_Syntax_matchesNull(v___x_4367_, v___x_4336_);
if (v___x_4369_ == 0)
{
lean_object* v___x_4370_; 
lean_dec(v___x_4367_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4370_;
}
else
{
lean_object* v___x_4371_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4371_ = l_Lean_Syntax_getArg(v___x_4367_, v___x_4247_);
lean_dec(v___x_4367_);
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4371_);
v___x_4373_ = l_Lean_Syntax_isOfKind(v___x_4371_, v___x_4372_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; 
lean_dec(v___x_4371_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4374_;
}
else
{
lean_object* v_patType_x3f_4375_; lean_object* v___x_4376_; 
v_patType_x3f_4375_ = l_Lean_Syntax_getArg(v___x_4371_, v___x_4336_);
lean_dec(v___x_4371_);
v___x_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4376_, 0, v_patType_x3f_4375_);
v_patType_x3f_4338_ = v___x_4376_;
v___y_4339_ = v_a_4231_;
v___y_4340_ = v_a_4232_;
v___y_4341_ = v_a_4233_;
v___y_4342_ = v_a_4234_;
v___y_4343_ = v_a_4235_;
v___y_4344_ = v_a_4236_;
v___y_4345_ = v_a_4237_;
goto v___jp_4337_;
}
}
}
else
{
lean_object* v___x_4377_; 
lean_dec(v___x_4367_);
v___x_4377_ = lean_box(0);
v_patType_x3f_4338_ = v___x_4377_;
v___y_4339_ = v_a_4231_;
v___y_4340_ = v_a_4232_;
v___y_4341_ = v_a_4233_;
v___y_4342_ = v_a_4234_;
v___y_4343_ = v_a_4235_;
v___y_4344_ = v_a_4236_;
v___y_4345_ = v_a_4237_;
goto v___jp_4337_;
}
v___jp_4337_:
{
lean_object* v___x_4346_; lean_object* v_rhs_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4346_ = lean_unsigned_to_nat(3u);
v_rhs_4347_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4346_);
v___x_4348_ = lean_unsigned_to_nat(4u);
v___x_4349_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4348_);
lean_dec(v_stx_4228_);
v___x_4350_ = l_Lean_Syntax_isNone(v___x_4349_);
if (v___x_4350_ == 0)
{
uint8_t v___x_4351_; 
lean_inc(v___x_4349_);
v___x_4351_ = l_Lean_Syntax_matchesNull(v___x_4349_, v___x_4346_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; 
lean_dec(v___x_4349_);
lean_dec(v_rhs_4347_);
lean_dec(v_patType_x3f_4338_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_letOrReassign_4227_);
v___x_4352_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4352_;
}
else
{
lean_object* v___x_4353_; lean_object* v_otherwise_x3f_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4353_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4354_ = l_Lean_Syntax_getArg(v___x_4349_, v___x_4336_);
v___x_4355_ = l_Lean_Syntax_getArg(v___x_4349_, v___x_4353_);
lean_dec(v___x_4349_);
v___x_4356_ = l_Lean_Syntax_getOptional_x3f(v___x_4355_);
lean_dec(v___x_4355_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_box(0);
v___y_4281_ = v___y_4343_;
v___y_4282_ = v_rhs_4347_;
v___y_4283_ = v___y_4339_;
v___y_4284_ = v_patType_x3f_4338_;
v___y_4285_ = v___y_4345_;
v___y_4286_ = v___y_4344_;
v___y_4287_ = v___y_4341_;
v___y_4288_ = v___y_4342_;
v___y_4289_ = v_otherwise_x3f_4354_;
v___y_4290_ = v___y_4340_;
v___y_4291_ = v___x_4357_;
goto v___jp_4280_;
}
else
{
lean_object* v_val_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
v_val_4358_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4356_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_val_4358_);
lean_dec(v___x_4356_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_val_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
v___y_4281_ = v___y_4343_;
v___y_4282_ = v_rhs_4347_;
v___y_4283_ = v___y_4339_;
v___y_4284_ = v_patType_x3f_4338_;
v___y_4285_ = v___y_4345_;
v___y_4286_ = v___y_4344_;
v___y_4287_ = v___y_4341_;
v___y_4288_ = v___y_4342_;
v___y_4289_ = v_otherwise_x3f_4354_;
v___y_4290_ = v___y_4340_;
v___y_4291_ = v___x_4363_;
goto v___jp_4280_;
}
}
}
}
}
else
{
lean_object* v___x_4366_; 
lean_dec(v___x_4349_);
v___x_4366_ = lean_box(0);
v___y_4252_ = v___y_4345_;
v___y_4253_ = v___y_4341_;
v___y_4254_ = v___y_4343_;
v___y_4255_ = v___y_4344_;
v___y_4256_ = v___y_4342_;
v___y_4257_ = v___y_4340_;
v___y_4258_ = v___x_4366_;
v___y_4259_ = v_patType_x3f_4338_;
v___y_4260_ = v___y_4339_;
v___y_4261_ = v_rhs_4347_;
v___y_4262_ = v___x_4366_;
goto v___jp_4251_;
}
}
}
else
{
lean_object* v_pattern_4378_; lean_object* v___x_4379_; lean_object* v_patType_x3f_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___x_4436_; uint8_t v___x_4437_; 
v_pattern_4378_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4247_);
v___x_4379_ = lean_unsigned_to_nat(1u);
v___x_4436_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4379_);
v___x_4437_ = l_Lean_Syntax_isNone(v___x_4436_);
if (v___x_4437_ == 0)
{
uint8_t v___x_4438_; 
lean_inc(v___x_4436_);
v___x_4438_ = l_Lean_Syntax_matchesNull(v___x_4436_, v___x_4379_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
lean_dec(v___x_4436_);
lean_dec(v_pattern_4378_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4439_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4439_;
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4440_ = l_Lean_Syntax_getArg(v___x_4436_, v___x_4247_);
lean_dec(v___x_4436_);
v___x_4441_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4440_);
v___x_4442_ = l_Lean_Syntax_isOfKind(v___x_4440_, v___x_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; 
lean_dec(v___x_4440_);
lean_dec(v_pattern_4378_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4443_;
}
else
{
lean_object* v_patType_x3f_4444_; lean_object* v___x_4445_; 
v_patType_x3f_4444_ = l_Lean_Syntax_getArg(v___x_4440_, v___x_4379_);
lean_dec(v___x_4440_);
v___x_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4445_, 0, v_patType_x3f_4444_);
v_patType_x3f_4381_ = v___x_4445_;
v___y_4382_ = v_a_4231_;
v___y_4383_ = v_a_4232_;
v___y_4384_ = v_a_4233_;
v___y_4385_ = v_a_4234_;
v___y_4386_ = v_a_4235_;
v___y_4387_ = v_a_4236_;
v___y_4388_ = v_a_4237_;
goto v___jp_4380_;
}
}
}
else
{
lean_object* v___x_4446_; 
lean_dec(v___x_4436_);
v___x_4446_ = lean_box(0);
v_patType_x3f_4381_ = v___x_4446_;
v___y_4382_ = v_a_4231_;
v___y_4383_ = v_a_4232_;
v___y_4384_ = v_a_4233_;
v___y_4385_ = v_a_4234_;
v___y_4386_ = v_a_4235_;
v___y_4387_ = v_a_4236_;
v___y_4388_ = v_a_4237_;
goto v___jp_4380_;
}
v___jp_4380_:
{
lean_object* v___x_4389_; lean_object* v_rhs_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4389_ = lean_unsigned_to_nat(3u);
v_rhs_4390_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4389_);
v___x_4391_ = lean_unsigned_to_nat(4u);
v___x_4392_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4391_);
lean_dec(v_stx_4228_);
lean_inc(v___x_4392_);
v___x_4393_ = l_Lean_Syntax_matchesNull(v___x_4392_, v___x_4247_);
if (v___x_4393_ == 0)
{
uint8_t v___x_4394_; 
lean_dec(v_pattern_4378_);
v___x_4394_ = l_Lean_Syntax_isNone(v___x_4392_);
if (v___x_4394_ == 0)
{
uint8_t v___x_4395_; 
lean_inc(v___x_4392_);
v___x_4395_ = l_Lean_Syntax_matchesNull(v___x_4392_, v___x_4389_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_dec(v___x_4392_);
lean_dec(v_rhs_4390_);
lean_dec(v_patType_x3f_4381_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_letOrReassign_4227_);
v___x_4396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4396_;
}
else
{
lean_object* v___x_4397_; lean_object* v_otherwise_x3f_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4397_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4398_ = l_Lean_Syntax_getArg(v___x_4392_, v___x_4379_);
v___x_4399_ = l_Lean_Syntax_getArg(v___x_4392_, v___x_4397_);
lean_dec(v___x_4392_);
v___x_4400_ = l_Lean_Syntax_getOptional_x3f(v___x_4399_);
lean_dec(v___x_4399_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_box(0);
v___y_4324_ = v_patType_x3f_4381_;
v___y_4325_ = v___y_4385_;
v___y_4326_ = v___y_4383_;
v___y_4327_ = v___y_4387_;
v___y_4328_ = v___y_4382_;
v___y_4329_ = v___y_4386_;
v___y_4330_ = v___y_4384_;
v___y_4331_ = v_rhs_4390_;
v___y_4332_ = v___y_4388_;
v___y_4333_ = v_otherwise_x3f_4398_;
v___y_4334_ = v___x_4401_;
goto v___jp_4323_;
}
else
{
lean_object* v_val_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_val_4402_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4400_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_val_4402_);
lean_dec(v___x_4400_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_val_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
v___y_4324_ = v_patType_x3f_4381_;
v___y_4325_ = v___y_4385_;
v___y_4326_ = v___y_4383_;
v___y_4327_ = v___y_4387_;
v___y_4328_ = v___y_4382_;
v___y_4329_ = v___y_4386_;
v___y_4330_ = v___y_4384_;
v___y_4331_ = v_rhs_4390_;
v___y_4332_ = v___y_4388_;
v___y_4333_ = v_otherwise_x3f_4398_;
v___y_4334_ = v___x_4407_;
goto v___jp_4323_;
}
}
}
}
}
else
{
lean_object* v___x_4410_; 
lean_dec(v___x_4392_);
v___x_4410_ = lean_box(0);
v___y_4294_ = v___y_4384_;
v___y_4295_ = v___y_4388_;
v___y_4296_ = v___y_4386_;
v___y_4297_ = v_rhs_4390_;
v___y_4298_ = v___y_4387_;
v___y_4299_ = v___y_4383_;
v___y_4300_ = v_patType_x3f_4381_;
v___y_4301_ = v___y_4385_;
v___y_4302_ = v___x_4410_;
v___y_4303_ = v___y_4382_;
v___y_4304_ = v___x_4410_;
goto v___jp_4293_;
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
lean_dec(v___x_4392_);
lean_dec(v___x_4248_);
lean_dec(v_letOrReassign_4227_);
v___x_4411_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4412_ = l_Lean_Core_mkFreshUserName(v___x_4411_, v___y_4387_, v___y_4388_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4230_, v_tk_4229_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; uint8_t v_kind_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref_known(v___x_4414_, 1);
v_kind_4416_ = lean_ctor_get_uint8(v_a_4415_, sizeof(void*)*3);
v___x_4417_ = l_Lean_mkIdentFrom(v_pattern_4378_, v_a_4413_, v___x_4243_);
lean_dec(v_pattern_4378_);
v___x_4418_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4418_, 0, v_a_4415_);
v___x_4419_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4417_, v_patType_x3f_4381_, v_rhs_4390_, v___x_4418_, v_kind_4416_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
return v___x_4419_;
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec(v_a_4413_);
lean_dec(v_rhs_4390_);
lean_dec(v_patType_x3f_4381_);
lean_dec(v_pattern_4378_);
v_a_4420_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4414_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4414_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec(v_rhs_4390_);
lean_dec(v_patType_x3f_4381_);
lean_dec(v_pattern_4378_);
lean_dec_ref(v_dec_4230_);
v_a_4428_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4412_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4412_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
}
}
v___jp_4251_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4264_ = l_Lean_Core_mkFreshUserName(v___x_4263_, v___y_4255_, v___y_4252_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___y_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v___x_4266_ = l_Lean_mkIdentFrom(v___x_4248_, v_a_4265_, v___x_4250_);
v___x_4267_ = lean_box(v___x_4250_);
v___x_4268_ = lean_box(v___x_4245_);
lean_inc(v___x_4266_);
v___y_4269_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4269_, 0, v_letOrReassign_4227_);
lean_closure_set(v___y_4269_, 1, v___y_4258_);
lean_closure_set(v___y_4269_, 2, v___x_4267_);
lean_closure_set(v___y_4269_, 3, v___x_4239_);
lean_closure_set(v___y_4269_, 4, v___x_4240_);
lean_closure_set(v___y_4269_, 5, v___x_4241_);
lean_closure_set(v___y_4269_, 6, v___x_4248_);
lean_closure_set(v___y_4269_, 7, v___x_4266_);
lean_closure_set(v___y_4269_, 8, v_dec_4230_);
lean_closure_set(v___y_4269_, 9, v___x_4268_);
lean_closure_set(v___y_4269_, 10, v___y_4262_);
lean_closure_set(v___y_4269_, 11, v___x_4247_);
v___x_4270_ = 0;
v___x_4271_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4266_, v___y_4259_, v___y_4261_, v___y_4269_, v___x_4270_, v___y_4260_, v___y_4257_, v___y_4253_, v___y_4256_, v___y_4254_, v___y_4255_, v___y_4252_);
return v___x_4271_;
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_letOrReassign_4227_);
v_a_4272_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4264_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4264_);
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
v___jp_4280_:
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4292_, 0, v___y_4289_);
v___y_4252_ = v___y_4285_;
v___y_4253_ = v___y_4287_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4288_;
v___y_4257_ = v___y_4290_;
v___y_4258_ = v___x_4292_;
v___y_4259_ = v___y_4284_;
v___y_4260_ = v___y_4283_;
v___y_4261_ = v___y_4282_;
v___y_4262_ = v___y_4291_;
goto v___jp_4251_;
}
v___jp_4293_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4306_ = l_Lean_Core_mkFreshUserName(v___x_4305_, v___y_4298_, v___y_4295_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___y_4312_; uint8_t v___x_4313_; lean_object* v___x_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_mkIdentFrom(v___x_4248_, v_a_4307_, v___x_4243_);
v___x_4309_ = lean_box(v___x_4243_);
v___x_4310_ = lean_box(v___x_4245_);
v___x_4311_ = lean_box(v___x_4250_);
lean_inc(v___x_4308_);
v___y_4312_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4312_, 0, v_letOrReassign_4227_);
lean_closure_set(v___y_4312_, 1, v___y_4302_);
lean_closure_set(v___y_4312_, 2, v___x_4309_);
lean_closure_set(v___y_4312_, 3, v___x_4239_);
lean_closure_set(v___y_4312_, 4, v___x_4240_);
lean_closure_set(v___y_4312_, 5, v___x_4241_);
lean_closure_set(v___y_4312_, 6, v___x_4248_);
lean_closure_set(v___y_4312_, 7, v___x_4308_);
lean_closure_set(v___y_4312_, 8, v_dec_4230_);
lean_closure_set(v___y_4312_, 9, v___x_4310_);
lean_closure_set(v___y_4312_, 10, v___y_4304_);
lean_closure_set(v___y_4312_, 11, v___x_4247_);
lean_closure_set(v___y_4312_, 12, v___x_4311_);
v___x_4313_ = 0;
v___x_4314_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4308_, v___y_4300_, v___y_4297_, v___y_4312_, v___x_4313_, v___y_4303_, v___y_4299_, v___y_4294_, v___y_4301_, v___y_4296_, v___y_4298_, v___y_4295_);
return v___x_4314_;
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v___y_4304_);
lean_dec(v___y_4302_);
lean_dec(v___y_4300_);
lean_dec(v___y_4297_);
lean_dec(v___x_4248_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_letOrReassign_4227_);
v_a_4315_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4306_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4306_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___y_4333_);
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4332_;
v___y_4296_ = v___y_4329_;
v___y_4297_ = v___y_4331_;
v___y_4298_ = v___y_4327_;
v___y_4299_ = v___y_4326_;
v___y_4300_ = v___y_4324_;
v___y_4301_ = v___y_4325_;
v___y_4302_ = v___x_4335_;
v___y_4303_ = v___y_4328_;
v___y_4304_ = v___y_4334_;
goto v___jp_4293_;
}
}
}
else
{
lean_object* v___x_4447_; lean_object* v_x_4448_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v_xType_x3f_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v_xType_x3f_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4447_ = lean_unsigned_to_nat(0u);
v_x_4448_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4447_);
v___x_4521_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4448_);
v___x_4522_ = l_Lean_Syntax_isOfKind(v_x_4448_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; 
lean_dec(v_x_4448_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = lean_unsigned_to_nat(1u);
v___x_4525_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4524_);
v___x_4526_ = l_Lean_Syntax_isNone(v___x_4525_);
if (v___x_4526_ == 0)
{
uint8_t v___x_4527_; 
lean_inc(v___x_4525_);
v___x_4527_ = l_Lean_Syntax_matchesNull(v___x_4525_, v___x_4524_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; 
lean_dec(v___x_4525_);
lean_dec(v_x_4448_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___x_4529_ = l_Lean_Syntax_getArg(v___x_4525_, v___x_4447_);
lean_dec(v___x_4525_);
v___x_4530_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4529_);
v___x_4531_ = l_Lean_Syntax_isOfKind(v___x_4529_, v___x_4530_);
if (v___x_4531_ == 0)
{
lean_object* v___x_4532_; 
lean_dec(v___x_4529_);
lean_dec(v_x_4448_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v___x_4532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4532_;
}
else
{
lean_object* v_xType_x3f_4533_; lean_object* v___x_4534_; 
v_xType_x3f_4533_ = l_Lean_Syntax_getArg(v___x_4529_, v___x_4524_);
lean_dec(v___x_4529_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_xType_x3f_4533_);
v_xType_x3f_4466_ = v___x_4534_;
v___y_4467_ = v_a_4231_;
v___y_4468_ = v_a_4232_;
v___y_4469_ = v_a_4233_;
v___y_4470_ = v_a_4234_;
v___y_4471_ = v_a_4235_;
v___y_4472_ = v_a_4236_;
v___y_4473_ = v_a_4237_;
goto v___jp_4465_;
}
}
}
else
{
lean_object* v___x_4535_; 
lean_dec(v___x_4525_);
v___x_4535_ = lean_box(0);
v_xType_x3f_4466_ = v___x_4535_;
v___y_4467_ = v_a_4231_;
v___y_4468_ = v_a_4232_;
v___y_4469_ = v_a_4233_;
v___y_4470_ = v_a_4234_;
v___y_4471_ = v_a_4235_;
v___y_4472_ = v_a_4236_;
v___y_4473_ = v_a_4237_;
goto v___jp_4465_;
}
}
v___jp_4449_:
{
uint8_t v_kind_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_kind_4460_ = lean_ctor_get_uint8(v___y_4451_, sizeof(void*)*3);
v___x_4461_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4227_);
lean_dec(v_letOrReassign_4227_);
v___x_4462_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4462_, 0, v___y_4451_);
lean_inc(v_x_4448_);
v___x_4463_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4463_, 0, lean_box(0));
lean_closure_set(v___x_4463_, 1, v___x_4461_);
lean_closure_set(v___x_4463_, 2, v_x_4448_);
lean_closure_set(v___x_4463_, 3, v___x_4462_);
v___x_4464_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4448_, v_xType_x3f_4452_, v___y_4450_, v___x_4463_, v_kind_4460_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
return v___x_4464_;
}
v___jp_4465_:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4474_ = lean_unsigned_to_nat(1u);
v___x_4475_ = lean_mk_empty_array_with_capacity(v___x_4474_);
lean_inc(v_x_4448_);
v___x_4476_ = lean_array_push(v___x_4475_, v_x_4448_);
v___x_4477_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4227_, v___x_4476_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec_ref(v___x_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v___x_4478_; 
lean_dec_ref_known(v___x_4477_, 1);
v___x_4478_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4230_, v_tk_4229_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v_rhs_4481_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = lean_unsigned_to_nat(3u);
v_rhs_4481_ = l_Lean_Syntax_getArg(v_stx_4228_, v___x_4480_);
lean_dec(v_stx_4228_);
if (lean_obj_tag(v_letOrReassign_4227_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4466_) == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = l_Lean_TSyntax_getId(v_x_4448_);
v___x_4483_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4482_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = l_Lean_LocalDecl_type(v_a_4484_);
lean_dec(v_a_4484_);
v___x_4486_ = l_Lean_Elab_Term_exprToSyntax(v___x_4485_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4488_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___x_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4488_, 0, v_a_4487_);
v___y_4450_ = v_rhs_4481_;
v___y_4451_ = v_a_4479_;
v_xType_x3f_4452_ = v___x_4488_;
v___y_4453_ = v___y_4467_;
v___y_4454_ = v___y_4468_;
v___y_4455_ = v___y_4469_;
v___y_4456_ = v___y_4470_;
v___y_4457_ = v___y_4471_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
goto v___jp_4449_;
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_rhs_4481_);
lean_dec(v_a_4479_);
lean_dec(v_x_4448_);
v_a_4489_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4486_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4486_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
lean_dec(v_rhs_4481_);
lean_dec(v_a_4479_);
lean_dec(v_x_4448_);
v_a_4497_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4483_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4483_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
else
{
v___y_4450_ = v_rhs_4481_;
v___y_4451_ = v_a_4479_;
v_xType_x3f_4452_ = v_xType_x3f_4466_;
v___y_4453_ = v___y_4467_;
v___y_4454_ = v___y_4468_;
v___y_4455_ = v___y_4469_;
v___y_4456_ = v___y_4470_;
v___y_4457_ = v___y_4471_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
goto v___jp_4449_;
}
}
else
{
v___y_4450_ = v_rhs_4481_;
v___y_4451_ = v_a_4479_;
v_xType_x3f_4452_ = v_xType_x3f_4466_;
v___y_4453_ = v___y_4467_;
v___y_4454_ = v___y_4468_;
v___y_4455_ = v___y_4469_;
v___y_4456_ = v___y_4470_;
v___y_4457_ = v___y_4471_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
goto v___jp_4449_;
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec(v_xType_x3f_4466_);
lean_dec(v_x_4448_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v_a_4505_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4478_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4478_);
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
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v_xType_x3f_4466_);
lean_dec(v_x_4448_);
lean_dec_ref(v_dec_4230_);
lean_dec(v_stx_4228_);
lean_dec(v_letOrReassign_4227_);
v_a_4513_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4477_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4477_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4536_, lean_object* v_stx_4537_, lean_object* v_tk_4538_, lean_object* v_dec_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4536_, v_stx_4537_, v_tk_4538_, v_dec_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_tk_4538_);
return v_res_4548_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4551_ = l_Lean_stringToMessageData(v___x_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4552_, lean_object* v_mutTk_x3f_4553_, lean_object* v_initConfig_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4553_) == 0)
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4552_, v_initConfig_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_);
return v___x_4562_;
}
else
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
v___x_4563_ = lean_unsigned_to_nat(0u);
v___x_4564_ = l_Lean_Syntax_getArg(v_letConfigStx_4552_, v___x_4563_);
v___x_4565_ = l_Lean_Syntax_getArgs(v___x_4564_);
lean_dec(v___x_4564_);
v___x_4566_ = lean_array_get_size(v___x_4565_);
lean_dec_ref(v___x_4565_);
v___x_4567_ = lean_nat_dec_eq(v___x_4566_, v___x_4563_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v_initConfig_4554_);
v___x_4568_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4569_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4552_, v___x_4568_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_);
lean_dec(v_letConfigStx_4552_);
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
else
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4552_, v_initConfig_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_);
return v___x_4578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4579_, lean_object* v_mutTk_x3f_4580_, lean_object* v_initConfig_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4579_, v_mutTk_x3f_4580_, v_initConfig_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_mutTk_x3f_4580_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4590_, lean_object* v_mutTk_x3f_4591_, lean_object* v_initConfig_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4590_, v_mutTk_x3f_4591_, v_initConfig_4592_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4602_, lean_object* v_mutTk_x3f_4603_, lean_object* v_initConfig_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4602_, v_mutTk_x3f_4603_, v_initConfig_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_mutTk_x3f_4603_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4627_, lean_object* v_dec_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; uint8_t v___x_4638_; 
v___x_4637_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4627_);
v___x_4638_ = l_Lean_Syntax_isOfKind(v_stx_4627_, v___x_4637_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; 
lean_dec_ref(v_dec_4628_);
lean_dec(v_stx_4627_);
v___x_4639_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4639_;
}
else
{
lean_object* v___x_4640_; lean_object* v_tk_4641_; lean_object* v_mutTk_x3f_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v___x_4640_ = lean_unsigned_to_nat(0u);
v_tk_4641_ = l_Lean_Syntax_getArg(v_stx_4627_, v___x_4640_);
v___x_4674_ = lean_unsigned_to_nat(1u);
v___x_4675_ = l_Lean_Syntax_getArg(v_stx_4627_, v___x_4674_);
v___x_4676_ = l_Lean_Syntax_isNone(v___x_4675_);
if (v___x_4676_ == 0)
{
uint8_t v___x_4677_; 
lean_inc(v___x_4675_);
v___x_4677_ = l_Lean_Syntax_matchesNull(v___x_4675_, v___x_4674_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; 
lean_dec(v___x_4675_);
lean_dec(v_tk_4641_);
lean_dec_ref(v_dec_4628_);
lean_dec(v_stx_4627_);
v___x_4678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4678_;
}
else
{
lean_object* v_mutTk_x3f_4679_; lean_object* v___x_4680_; 
v_mutTk_x3f_4679_ = l_Lean_Syntax_getArg(v___x_4675_, v___x_4640_);
lean_dec(v___x_4675_);
v___x_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4680_, 0, v_mutTk_x3f_4679_);
v_mutTk_x3f_4643_ = v___x_4680_;
v___y_4644_ = v_a_4629_;
v___y_4645_ = v_a_4630_;
v___y_4646_ = v_a_4631_;
v___y_4647_ = v_a_4632_;
v___y_4648_ = v_a_4633_;
v___y_4649_ = v_a_4634_;
v___y_4650_ = v_a_4635_;
goto v___jp_4642_;
}
}
else
{
lean_object* v___x_4681_; 
lean_dec(v___x_4675_);
v___x_4681_ = lean_box(0);
v_mutTk_x3f_4643_ = v___x_4681_;
v___y_4644_ = v_a_4629_;
v___y_4645_ = v_a_4630_;
v___y_4646_ = v_a_4631_;
v___y_4647_ = v_a_4632_;
v___y_4648_ = v_a_4633_;
v___y_4649_ = v_a_4634_;
v___y_4650_ = v_a_4635_;
goto v___jp_4642_;
}
v___jp_4642_:
{
lean_object* v___x_4651_; lean_object* v_config_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4651_ = lean_unsigned_to_nat(2u);
v_config_4652_ = l_Lean_Syntax_getArg(v_stx_4627_, v___x_4651_);
v___x_4653_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4652_);
v___x_4654_ = l_Lean_Syntax_isOfKind(v_config_4652_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
lean_dec(v_config_4652_);
lean_dec(v_mutTk_x3f_4643_);
lean_dec(v_tk_4641_);
lean_dec_ref(v_dec_4628_);
lean_dec(v_stx_4627_);
v___x_4655_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v_decl_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4656_ = lean_unsigned_to_nat(3u);
v_decl_4657_ = l_Lean_Syntax_getArg(v_stx_4627_, v___x_4656_);
lean_dec(v_stx_4627_);
v___x_4658_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4657_);
v___x_4659_ = l_Lean_Syntax_isOfKind(v_decl_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; 
lean_dec(v_decl_4657_);
lean_dec(v_config_4652_);
lean_dec(v_mutTk_x3f_4643_);
lean_dec(v_tk_4641_);
lean_dec_ref(v_dec_4628_);
v___x_4660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4662_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4652_, v_mutTk_x3f_4643_, v___x_4661_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v_mutTk_x3f_4643_);
v___x_4665_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4663_, v___x_4664_, v_decl_4657_, v_tk_4641_, v_dec_4628_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
return v___x_4665_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec(v_decl_4657_);
lean_dec(v_mutTk_x3f_4643_);
lean_dec(v_tk_4641_);
lean_dec_ref(v_dec_4628_);
v_a_4666_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4662_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4662_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4682_, lean_object* v_dec_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Elab_Do_elabDoLet(v_stx_4682_, v_dec_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec_ref(v_a_4684_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4700_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4701_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4702_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4703_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4704_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4700_, v___x_4701_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4712_, lean_object* v_dec_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v___x_4722_; uint8_t v___x_4723_; 
v___x_4722_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4712_);
v___x_4723_ = l_Lean_Syntax_isOfKind(v_stx_4712_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4724_; 
lean_dec_ref(v_dec_4713_);
lean_dec(v_stx_4712_);
v___x_4724_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4724_;
}
else
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4725_ = lean_unsigned_to_nat(1u);
v___x_4726_ = l_Lean_Syntax_getArg(v_stx_4712_, v___x_4725_);
v___x_4727_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4726_);
v___x_4728_ = l_Lean_Syntax_isOfKind(v___x_4726_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; 
lean_dec(v___x_4726_);
lean_dec_ref(v_dec_4713_);
lean_dec(v_stx_4712_);
v___x_4729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4729_;
}
else
{
lean_object* v___x_4730_; lean_object* v_decl_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4730_ = lean_unsigned_to_nat(2u);
v_decl_4731_ = l_Lean_Syntax_getArg(v_stx_4712_, v___x_4730_);
v___x_4732_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4731_);
v___x_4733_ = l_Lean_Syntax_isOfKind(v_decl_4731_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; 
lean_dec(v_decl_4731_);
lean_dec(v___x_4726_);
lean_dec_ref(v_dec_4713_);
lean_dec(v_stx_4712_);
v___x_4734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4734_;
}
else
{
uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4735_ = 0;
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*1, v___x_4733_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*1 + 1, v___x_4735_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*1 + 2, v___x_4735_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*1 + 3, v___x_4735_);
lean_ctor_set_uint8(v___x_4737_, sizeof(void*)*1 + 4, v___x_4735_);
v___x_4738_ = l_Lean_Elab_Term_mkLetConfig(v___x_4726_, v___x_4737_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v___x_4740_; lean_object* v_tk_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4738_, 1);
v___x_4740_ = lean_unsigned_to_nat(0u);
v_tk_4741_ = l_Lean_Syntax_getArg(v_stx_4712_, v___x_4740_);
lean_dec(v_stx_4712_);
v___x_4742_ = lean_box(1);
v___x_4743_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4739_, v___x_4742_, v_decl_4731_, v_tk_4741_, v_dec_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4743_;
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_decl_4731_);
lean_dec_ref(v_dec_4713_);
lean_dec(v_stx_4712_);
v_a_4744_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4738_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4738_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4752_, lean_object* v_dec_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Elab_Do_elabDoHave(v_stx_4752_, v_dec_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec_ref(v_a_4754_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4770_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4771_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4772_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4773_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4774_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4770_, v___x_4771_, v___x_4772_, v___x_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4779_, lean_object* v___x_4780_, lean_object* v___x_4781_, lean_object* v___x_4782_, lean_object* v_decls_4783_, lean_object* v_a_4784_, uint8_t v___x_4785_, lean_object* v_body_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v_ref_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v_ref_4795_ = lean_ctor_get(v___y_4792_, 2);
v___x_4796_ = 0;
v___x_4797_ = l_Lean_SourceInfo_fromRef(v_ref_4795_, v___x_4796_);
v___x_4798_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4799_ = l_Lean_Name_mkStr4(v___x_4779_, v___x_4780_, v___x_4781_, v___x_4798_);
v___x_4800_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4797_, 4);
v___x_4801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4797_);
lean_ctor_set(v___x_4801_, 1, v___x_4800_);
v___x_4802_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4797_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = l_Lean_Syntax_node2(v___x_4797_, v___x_4782_, v___x_4801_, v___x_4803_);
v___x_4805_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4797_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = l_Lean_Syntax_node4(v___x_4797_, v___x_4799_, v___x_4804_, v_decls_4783_, v___x_4806_, v_body_4786_);
v___x_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4808_, 0, v_a_4784_);
v___x_4809_ = l_Lean_Elab_Term_elabTerm(v___x_4807_, v___x_4808_, v___x_4785_, v___x_4785_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4810_, lean_object* v___x_4811_, lean_object* v___x_4812_, lean_object* v___x_4813_, lean_object* v_decls_4814_, lean_object* v_a_4815_, lean_object* v___x_4816_, lean_object* v_body_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
uint8_t v___x_4487__boxed_4826_; lean_object* v_res_4827_; 
v___x_4487__boxed_4826_ = lean_unbox(v___x_4816_);
v_res_4827_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4810_, v___x_4811_, v___x_4812_, v___x_4813_, v_decls_4814_, v_a_4815_, v___x_4487__boxed_4826_, v_body_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v___y_4818_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4828_, lean_object* v_a_4829_){
_start:
{
if (lean_obj_tag(v_a_4828_) == 0)
{
lean_object* v___x_4830_; 
v___x_4830_ = l_List_reverse___redArg(v_a_4829_);
return v___x_4830_;
}
else
{
lean_object* v_head_4831_; lean_object* v_tail_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4841_; 
v_head_4831_ = lean_ctor_get(v_a_4828_, 0);
v_tail_4832_ = lean_ctor_get(v_a_4828_, 1);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_a_4828_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4834_ = v_a_4828_;
v_isShared_4835_ = v_isSharedCheck_4841_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_tail_4832_);
lean_inc(v_head_4831_);
lean_dec(v_a_4828_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4841_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4836_ = l_Lean_MessageData_ofSyntax(v_head_4831_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 1, v_a_4829_);
lean_ctor_set(v___x_4834_, 0, v___x_4836_);
v___x_4838_ = v___x_4834_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v_a_4829_);
v___x_4838_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
v_a_4828_ = v_tail_4832_;
v_a_4829_ = v___x_4838_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4859_ = l_Lean_stringToMessageData(v___x_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4860_, lean_object* v_dec_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v___x_4870_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4871_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4872_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4873_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4860_);
v___x_4874_ = l_Lean_Syntax_isOfKind(v_stx_4860_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; 
lean_dec_ref(v_dec_4861_);
lean_dec(v_stx_4860_);
v___x_4875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4876_ = lean_unsigned_to_nat(0u);
v___x_4877_ = l_Lean_Syntax_getArg(v_stx_4860_, v___x_4876_);
v___x_4878_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4877_);
v___x_4879_ = l_Lean_Syntax_isOfKind(v___x_4877_, v___x_4878_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; 
lean_dec(v___x_4877_);
lean_dec_ref(v_dec_4861_);
lean_dec(v_stx_4860_);
v___x_4880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4880_;
}
else
{
lean_object* v___x_4881_; lean_object* v_decls_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4881_ = lean_unsigned_to_nat(1u);
v_decls_4882_ = l_Lean_Syntax_getArg(v_stx_4860_, v___x_4881_);
lean_dec(v_stx_4860_);
v___x_4883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4882_);
v___x_4884_ = l_Lean_Syntax_isOfKind(v_decls_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; 
lean_dec(v_decls_4882_);
lean_dec(v___x_4877_);
lean_dec_ref(v_dec_4861_);
v___x_4885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4885_;
}
else
{
lean_object* v_tk_4886_; lean_object* v___x_4887_; 
v_tk_4886_ = l_Lean_Syntax_getArg(v___x_4877_, v___x_4876_);
lean_dec(v___x_4877_);
v___x_4887_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4861_, v_tk_4886_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
lean_dec(v_tk_4886_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4889_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
lean_inc(v_decls_4882_);
v___x_4889_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4882_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v_doBlockResultType_4891_; lean_object* v___x_4892_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v_doBlockResultType_4891_ = lean_ctor_get(v_a_4862_, 3);
lean_inc_ref(v_doBlockResultType_4891_);
v___x_4892_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4891_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4894_; lean_object* v___f_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4894_ = lean_box(v___x_4884_);
v___f_4895_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4895_, 0, v___x_4870_);
lean_closure_set(v___f_4895_, 1, v___x_4871_);
lean_closure_set(v___f_4895_, 2, v___x_4872_);
lean_closure_set(v___f_4895_, 3, v___x_4878_);
lean_closure_set(v___f_4895_, 4, v_decls_4882_);
lean_closure_set(v___f_4895_, 5, v_a_4893_);
lean_closure_set(v___f_4895_, 6, v___x_4894_);
v___x_4896_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4897_ = lean_array_to_list(v_a_4890_);
v___x_4898_ = lean_box(0);
v___x_4899_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4897_, v___x_4898_);
v___x_4900_ = l_Lean_MessageData_ofList(v___x_4899_);
v___x_4901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4896_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
v___x_4902_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4902_, 0, v_a_4888_);
v___x_4903_ = lean_box(0);
v___x_4904_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4901_, v___x_4902_, v___f_4895_, v___x_4903_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
return v___x_4904_;
}
else
{
lean_dec(v_a_4890_);
lean_dec(v_a_4888_);
lean_dec(v_decls_4882_);
return v___x_4892_;
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v_a_4888_);
lean_dec(v_decls_4882_);
v_a_4905_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4889_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4889_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_decls_4882_);
v_a_4913_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4887_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4887_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4921_, lean_object* v_dec_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4921_, v_dec_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
lean_dec_ref(v_a_4923_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4939_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4940_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4941_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4942_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4943_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4939_, v___x_4940_, v___x_4941_, v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4959_, lean_object* v_dec_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___y_4970_; lean_object* v___y_4971_; uint8_t v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
v___x_5002_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4959_);
v___x_5003_ = l_Lean_Syntax_isOfKind(v_stx_4959_, v___x_5002_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
lean_dec_ref(v_dec_4960_);
lean_dec(v_stx_4959_);
v___x_5004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5004_;
}
else
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5005_ = lean_unsigned_to_nat(0u);
v___x_5006_ = l_Lean_Syntax_getArg(v_stx_4959_, v___x_5005_);
lean_dec(v_stx_4959_);
v___x_5007_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5006_);
v___x_5008_ = l_Lean_Syntax_isOfKind(v___x_5006_, v___x_5007_);
if (v___x_5008_ == 0)
{
if (v___x_5008_ == 0)
{
lean_object* v___x_5020_; uint8_t v___x_5021_; 
v___x_5020_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5006_);
v___x_5021_ = l_Lean_Syntax_isOfKind(v___x_5006_, v___x_5020_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5022_;
}
else
{
goto v___jp_5009_;
}
}
else
{
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5023_ = l_Lean_Syntax_getArg(v___x_5006_, v___x_5005_);
v___x_5024_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5023_);
v___x_5025_ = l_Lean_Syntax_isOfKind(v___x_5023_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
lean_dec(v___x_5023_);
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5026_;
}
else
{
lean_object* v___x_5027_; lean_object* v_xType_x3f_5029_; lean_object* v___y_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v___x_5027_ = l_Lean_Syntax_getArg(v___x_5023_, v___x_5005_);
lean_dec(v___x_5023_);
v___x_5056_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5027_);
v___x_5057_ = l_Lean_Syntax_isOfKind(v___x_5027_, v___x_5056_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_dec(v___x_5027_);
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5058_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5058_;
}
else
{
lean_object* v___x_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v___x_5059_ = lean_unsigned_to_nat(1u);
v___x_5060_ = l_Lean_Syntax_getArg(v___x_5006_, v___x_5059_);
v___x_5061_ = l_Lean_Syntax_matchesNull(v___x_5060_, v___x_5005_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
lean_dec(v___x_5027_);
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5062_;
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v___x_5063_ = lean_unsigned_to_nat(2u);
v___x_5064_ = l_Lean_Syntax_getArg(v___x_5006_, v___x_5063_);
v___x_5065_ = l_Lean_Syntax_isNone(v___x_5064_);
if (v___x_5065_ == 0)
{
uint8_t v___x_5066_; 
lean_inc(v___x_5064_);
v___x_5066_ = l_Lean_Syntax_matchesNull(v___x_5064_, v___x_5059_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
lean_dec(v___x_5064_);
lean_dec(v___x_5027_);
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5067_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v___x_5068_ = l_Lean_Syntax_getArg(v___x_5064_, v___x_5005_);
lean_dec(v___x_5064_);
v___x_5069_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5068_);
v___x_5070_ = l_Lean_Syntax_isOfKind(v___x_5068_, v___x_5069_);
if (v___x_5070_ == 0)
{
lean_object* v___x_5071_; 
lean_dec(v___x_5068_);
lean_dec(v___x_5027_);
lean_dec(v___x_5006_);
lean_dec_ref(v_dec_4960_);
v___x_5071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5071_;
}
else
{
lean_object* v_xType_x3f_5072_; lean_object* v___x_5073_; 
v_xType_x3f_5072_ = l_Lean_Syntax_getArg(v___x_5068_, v___x_5059_);
lean_dec(v___x_5068_);
v___x_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5073_, 0, v_xType_x3f_5072_);
v_xType_x3f_5029_ = v___x_5073_;
v___y_5030_ = v_a_4961_;
v___y_5031_ = v_a_4962_;
v___y_5032_ = v_a_4963_;
v___y_5033_ = v_a_4964_;
v___y_5034_ = v_a_4965_;
v___y_5035_ = v_a_4966_;
v___y_5036_ = v_a_4967_;
goto v___jp_5028_;
}
}
}
else
{
lean_object* v___x_5074_; 
lean_dec(v___x_5064_);
v___x_5074_ = lean_box(0);
v_xType_x3f_5029_ = v___x_5074_;
v___y_5030_ = v_a_4961_;
v___y_5031_ = v_a_4962_;
v___y_5032_ = v_a_4963_;
v___y_5033_ = v_a_4964_;
v___y_5034_ = v_a_4965_;
v___y_5035_ = v_a_4966_;
v___y_5036_ = v_a_4967_;
goto v___jp_5028_;
}
}
}
v___jp_5028_:
{
lean_object* v_ref_5037_; lean_object* v___x_5038_; lean_object* v_tk_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; uint8_t v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v_ref_5037_ = lean_ctor_get(v___y_5035_, 2);
v___x_5038_ = lean_unsigned_to_nat(3u);
v_tk_5039_ = l_Lean_Syntax_getArg(v___x_5006_, v___x_5038_);
v___x_5040_ = lean_unsigned_to_nat(4u);
v___x_5041_ = l_Lean_Syntax_getArg(v___x_5006_, v___x_5040_);
lean_dec(v___x_5006_);
v___x_5042_ = 0;
v___x_5043_ = l_Lean_SourceInfo_fromRef(v_ref_5037_, v___x_5042_);
v___x_5044_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5043_, 2);
v___x_5045_ = l_Lean_Syntax_node1(v___x_5043_, v___x_5024_, v___x_5027_);
v___x_5046_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5047_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5048_, 0, v___x_5043_);
lean_ctor_set(v___x_5048_, 1, v___x_5046_);
lean_ctor_set(v___x_5048_, 2, v___x_5047_);
if (lean_obj_tag(v_xType_x3f_5029_) == 1)
{
lean_object* v_val_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v_val_5049_ = lean_ctor_get(v_xType_x3f_5029_, 0);
lean_inc(v_val_5049_);
lean_dec_ref_known(v_xType_x3f_5029_, 1);
v___x_5050_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5051_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5043_, 2);
v___x_5052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5043_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = l_Lean_Syntax_node2(v___x_5043_, v___x_5050_, v___x_5052_, v_val_5049_);
v___x_5054_ = l_Array_mkArray1___redArg(v___x_5053_);
v___y_4970_ = v___x_5048_;
v___y_4971_ = v___x_5044_;
v___y_4972_ = v___x_5042_;
v___y_4973_ = v___x_5043_;
v___y_4974_ = v___x_5045_;
v___y_4975_ = v___x_5047_;
v___y_4976_ = v___y_5034_;
v___y_4977_ = v___y_5033_;
v___y_4978_ = v___y_5036_;
v___y_4979_ = v_tk_5039_;
v___y_4980_ = v___y_5031_;
v___y_4981_ = v___x_5046_;
v___y_4982_ = v___x_5041_;
v___y_4983_ = v___y_5030_;
v___y_4984_ = v___y_5032_;
v___y_4985_ = v___y_5035_;
v___y_4986_ = v___x_5054_;
goto v___jp_4969_;
}
else
{
lean_object* v___x_5055_; 
lean_dec(v_xType_x3f_5029_);
v___x_5055_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4970_ = v___x_5048_;
v___y_4971_ = v___x_5044_;
v___y_4972_ = v___x_5042_;
v___y_4973_ = v___x_5043_;
v___y_4974_ = v___x_5045_;
v___y_4975_ = v___x_5047_;
v___y_4976_ = v___y_5034_;
v___y_4977_ = v___y_5033_;
v___y_4978_ = v___y_5036_;
v___y_4979_ = v_tk_5039_;
v___y_4980_ = v___y_5031_;
v___y_4981_ = v___x_5046_;
v___y_4982_ = v___x_5041_;
v___y_4983_ = v___y_5030_;
v___y_4984_ = v___y_5032_;
v___y_4985_ = v___y_5035_;
v___y_4986_ = v___x_5055_;
goto v___jp_4969_;
}
}
}
}
v___jp_5009_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v_decl_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5010_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5011_ = lean_unsigned_to_nat(1u);
v___x_5012_ = lean_mk_empty_array_with_capacity(v___x_5011_);
v___x_5013_ = lean_array_push(v___x_5012_, v___x_5006_);
v___x_5014_ = lean_box(2);
v_decl_5015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5015_, 0, v___x_5014_);
lean_ctor_set(v_decl_5015_, 1, v___x_5010_);
lean_ctor_set(v_decl_5015_, 2, v___x_5013_);
v___x_5016_ = lean_box(0);
v___x_5017_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1, v___x_5008_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1 + 1, v___x_5008_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1 + 2, v___x_5008_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1 + 3, v___x_5008_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1 + 4, v___x_5008_);
v___x_5018_ = lean_box(2);
lean_inc_ref(v_decl_5015_);
v___x_5019_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5017_, v___x_5018_, v_decl_5015_, v_decl_5015_, v_dec_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
return v___x_5019_;
}
}
v___jp_4969_:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
lean_inc_ref(v___y_4975_);
v___x_4987_ = l_Array_append___redArg(v___y_4975_, v___y_4986_);
lean_dec_ref(v___y_4986_);
lean_inc(v___y_4981_);
lean_inc_n(v___y_4973_, 2);
v___x_4988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4988_, 0, v___y_4973_);
lean_ctor_set(v___x_4988_, 1, v___y_4981_);
lean_ctor_set(v___x_4988_, 2, v___x_4987_);
v___x_4989_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___y_4973_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
lean_inc(v___y_4971_);
v___x_4991_ = l_Lean_Syntax_node5(v___y_4973_, v___y_4971_, v___y_4974_, v___y_4970_, v___x_4988_, v___x_4990_, v___y_4982_);
v___x_4992_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4993_ = lean_unsigned_to_nat(1u);
v___x_4994_ = lean_mk_empty_array_with_capacity(v___x_4993_);
v___x_4995_ = lean_array_push(v___x_4994_, v___x_4991_);
v___x_4996_ = lean_box(2);
v___x_4997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
lean_ctor_set(v___x_4997_, 1, v___x_4992_);
lean_ctor_set(v___x_4997_, 2, v___x_4995_);
v___x_4998_ = lean_box(0);
v___x_4999_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1, v___y_4972_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1 + 1, v___y_4972_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1 + 2, v___y_4972_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1 + 3, v___y_4972_);
lean_ctor_set_uint8(v___x_4999_, sizeof(void*)*1 + 4, v___y_4972_);
v___x_5000_ = lean_box(2);
v___x_5001_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4999_, v___x_5000_, v___x_4997_, v___y_4979_, v_dec_4960_, v___y_4983_, v___y_4980_, v___y_4984_, v___y_4977_, v___y_4976_, v___y_4985_, v___y_4978_);
return v___x_5001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5075_, lean_object* v_dec_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5075_, v_dec_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
lean_dec_ref(v_a_5077_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5093_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5094_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5095_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5096_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5097_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5093_, v___x_5094_, v___x_5095_, v___x_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
uint8_t v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5109_ = 0;
v___x_5110_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5100_, v___x_5109_);
v___x_5111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5111_, 0, v___x_5110_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v_____do__lift_5112_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5141_, size_t v_sz_5142_, size_t v_i_5143_, lean_object* v_b_5144_, lean_object* v___y_5145_){
_start:
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_usize_dec_lt(v_i_5143_, v_sz_5142_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; 
v___x_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5148_, 0, v_b_5144_);
return v___x_5148_;
}
else
{
lean_object* v_ref_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v_a_5152_; uint8_t v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; size_t v___x_5186_; size_t v___x_5187_; 
v_ref_5149_ = lean_ctor_get(v___y_5145_, 2);
v___x_5150_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5152_ = lean_array_uget_borrowed(v_as_5141_, v_i_5143_);
v___x_5153_ = 0;
v___x_5154_ = l_Lean_SourceInfo_fromRef(v_ref_5149_, v___x_5153_);
v___x_5155_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5157_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5158_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5154_, 17);
v___x_5159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5154_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5154_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5155_, v___x_5161_);
v___x_5163_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5154_);
lean_ctor_set(v___x_5164_, 1, v___x_5155_);
lean_ctor_set(v___x_5164_, 2, v___x_5163_);
lean_inc_ref_n(v___x_5164_, 3);
v___x_5165_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5150_, v___x_5164_);
v___x_5166_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5167_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5168_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5152_, 2);
v___x_5169_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5168_, v_a_5152_);
v___x_5170_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5154_);
lean_ctor_set(v___x_5171_, 1, v___x_5170_);
v___x_5172_ = l_Lean_Syntax_node5(v___x_5154_, v___x_5167_, v___x_5169_, v___x_5164_, v___x_5164_, v___x_5171_, v_a_5152_);
v___x_5173_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5166_, v___x_5172_);
v___x_5174_ = l_Lean_Syntax_node4(v___x_5154_, v___x_5157_, v___x_5159_, v___x_5162_, v___x_5165_, v___x_5173_);
v___x_5175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5154_);
lean_ctor_set(v___x_5176_, 1, v___x_5175_);
v___x_5177_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5155_, v___x_5176_);
v___x_5178_ = l_Lean_Syntax_node2(v___x_5154_, v___x_5156_, v___x_5174_, v___x_5177_);
v___x_5179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5154_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = l_Lean_Syntax_node2(v___x_5154_, v___x_5179_, v___x_5181_, v_b_5144_);
v___x_5183_ = l_Lean_Syntax_node2(v___x_5154_, v___x_5156_, v___x_5182_, v___x_5164_);
v___x_5184_ = l_Lean_Syntax_node2(v___x_5154_, v___x_5155_, v___x_5178_, v___x_5183_);
v___x_5185_ = l_Lean_Syntax_node1(v___x_5154_, v___x_5151_, v___x_5184_);
v___x_5186_ = ((size_t)1ULL);
v___x_5187_ = lean_usize_add(v_i_5143_, v___x_5186_);
v_i_5143_ = v___x_5187_;
v_b_5144_ = v___x_5185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5189_, lean_object* v_sz_5190_, lean_object* v_i_5191_, lean_object* v_b_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
size_t v_sz_boxed_5195_; size_t v_i_boxed_5196_; lean_object* v_res_5197_; 
v_sz_boxed_5195_ = lean_unbox_usize(v_sz_5190_);
lean_dec(v_sz_5190_);
v_i_boxed_5196_ = lean_unbox_usize(v_i_5191_);
lean_dec(v_i_5191_);
v_res_5197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5189_, v_sz_boxed_5195_, v_i_boxed_5196_, v_b_5192_, v___y_5193_);
lean_dec_ref(v___y_5193_);
lean_dec_ref(v_as_5189_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5198_, size_t v_sz_5199_, size_t v_i_5200_, lean_object* v_b_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
uint8_t v___x_5210_; 
v___x_5210_ = lean_usize_dec_lt(v_i_5200_, v_sz_5199_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
v___x_5211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5211_, 0, v_b_5201_);
return v___x_5211_;
}
else
{
lean_object* v_ref_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v_a_5215_; uint8_t v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; size_t v___x_5249_; size_t v___x_5250_; lean_object* v___x_5251_; 
v_ref_5212_ = lean_ctor_get(v___y_5207_, 2);
v___x_5213_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5215_ = lean_array_uget_borrowed(v_as_5198_, v_i_5200_);
v___x_5216_ = 0;
v___x_5217_ = l_Lean_SourceInfo_fromRef(v_ref_5212_, v___x_5216_);
v___x_5218_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5220_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5221_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5217_, 17);
v___x_5222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5217_);
lean_ctor_set(v___x_5222_, 1, v___x_5221_);
v___x_5223_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5217_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5218_, v___x_5224_);
v___x_5226_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5217_);
lean_ctor_set(v___x_5227_, 1, v___x_5218_);
lean_ctor_set(v___x_5227_, 2, v___x_5226_);
lean_inc_ref_n(v___x_5227_, 3);
v___x_5228_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5213_, v___x_5227_);
v___x_5229_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5230_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5231_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5215_, 2);
v___x_5232_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5231_, v_a_5215_);
v___x_5233_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5217_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
v___x_5235_ = l_Lean_Syntax_node5(v___x_5217_, v___x_5230_, v___x_5232_, v___x_5227_, v___x_5227_, v___x_5234_, v_a_5215_);
v___x_5236_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5229_, v___x_5235_);
v___x_5237_ = l_Lean_Syntax_node4(v___x_5217_, v___x_5220_, v___x_5222_, v___x_5225_, v___x_5228_, v___x_5236_);
v___x_5238_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5217_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5218_, v___x_5239_);
v___x_5241_ = l_Lean_Syntax_node2(v___x_5217_, v___x_5219_, v___x_5237_, v___x_5240_);
v___x_5242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5217_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = l_Lean_Syntax_node2(v___x_5217_, v___x_5242_, v___x_5244_, v_b_5201_);
v___x_5246_ = l_Lean_Syntax_node2(v___x_5217_, v___x_5219_, v___x_5245_, v___x_5227_);
v___x_5247_ = l_Lean_Syntax_node2(v___x_5217_, v___x_5218_, v___x_5241_, v___x_5246_);
v___x_5248_ = l_Lean_Syntax_node1(v___x_5217_, v___x_5214_, v___x_5247_);
v___x_5249_ = ((size_t)1ULL);
v___x_5250_ = lean_usize_add(v_i_5200_, v___x_5249_);
v___x_5251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5198_, v_sz_5199_, v___x_5250_, v___x_5248_, v___y_5207_);
return v___x_5251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5252_, lean_object* v_sz_5253_, lean_object* v_i_5254_, lean_object* v_b_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
size_t v_sz_boxed_5264_; size_t v_i_boxed_5265_; lean_object* v_res_5266_; 
v_sz_boxed_5264_ = lean_unbox_usize(v_sz_5253_);
lean_dec(v_sz_5253_);
v_i_boxed_5265_ = lean_unbox_usize(v_i_5254_);
lean_dec(v_i_5254_);
v_res_5266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5252_, v_sz_boxed_5264_, v_i_boxed_5265_, v_b_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec_ref(v_as_5252_);
return v_res_5266_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5307_ = l_String_toRawSubstring_x27(v___x_5306_);
return v___x_5307_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; 
v___x_5321_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5322_ = l_String_toRawSubstring_x27(v___x_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5339_, lean_object* v_dec_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v___x_5349_; uint8_t v___x_5350_; 
v___x_5349_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5339_);
v___x_5350_ = l_Lean_Syntax_isOfKind(v_stx_5339_, v___x_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
lean_dec_ref(v_dec_5340_);
lean_dec(v_stx_5339_);
v___x_5351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5351_;
}
else
{
uint8_t v___y_5353_; lean_object* v___y_5354_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v_body_5358_; lean_object* v___y_5359_; lean_object* v___y_5360_; lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v___y_5363_; lean_object* v___y_5364_; lean_object* v___y_5365_; lean_object* v___y_5439_; lean_object* v___y_5440_; lean_object* v___y_5441_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v___y_5445_; lean_object* v___y_5446_; uint8_t v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v_a_5453_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5470_; lean_object* v___y_5471_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5474_; lean_object* v___y_5475_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v_mutTk_x3f_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___x_5583_; lean_object* v___x_5584_; uint8_t v___x_5585_; 
v___x_5583_ = lean_unsigned_to_nat(1u);
v___x_5584_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5583_);
v___x_5585_ = l_Lean_Syntax_isNone(v___x_5584_);
if (v___x_5585_ == 0)
{
uint8_t v___x_5586_; 
lean_inc(v___x_5584_);
v___x_5586_ = l_Lean_Syntax_matchesNull(v___x_5584_, v___x_5583_);
if (v___x_5586_ == 0)
{
lean_object* v___x_5587_; 
lean_dec(v___x_5584_);
lean_dec_ref(v_dec_5340_);
lean_dec(v_stx_5339_);
v___x_5587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5587_;
}
else
{
lean_object* v___x_5588_; lean_object* v_mutTk_x3f_5589_; lean_object* v___x_5590_; 
v___x_5588_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5589_ = l_Lean_Syntax_getArg(v___x_5584_, v___x_5588_);
lean_dec(v___x_5584_);
v___x_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5590_, 0, v_mutTk_x3f_5589_);
v_mutTk_x3f_5552_ = v___x_5590_;
v___y_5553_ = v_a_5341_;
v___y_5554_ = v_a_5342_;
v___y_5555_ = v_a_5343_;
v___y_5556_ = v_a_5344_;
v___y_5557_ = v_a_5345_;
v___y_5558_ = v_a_5346_;
v___y_5559_ = v_a_5347_;
goto v___jp_5551_;
}
}
else
{
lean_object* v___x_5591_; 
lean_dec(v___x_5584_);
v___x_5591_ = lean_box(0);
v_mutTk_x3f_5552_ = v___x_5591_;
v___y_5553_ = v_a_5341_;
v___y_5554_ = v_a_5342_;
v___y_5555_ = v_a_5343_;
v___y_5556_ = v_a_5344_;
v___y_5557_ = v_a_5345_;
v___y_5558_ = v_a_5346_;
v___y_5559_ = v_a_5347_;
goto v___jp_5551_;
}
v___jp_5352_:
{
lean_object* v_eq_x3f_5366_; 
v_eq_x3f_5366_ = lean_ctor_get(v___y_5355_, 0);
lean_inc(v_eq_x3f_5366_);
lean_dec_ref(v___y_5355_);
if (lean_obj_tag(v_eq_x3f_5366_) == 1)
{
lean_object* v_val_5367_; lean_object* v_ref_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v_val_5367_ = lean_ctor_get(v_eq_x3f_5366_, 0);
lean_inc(v_val_5367_);
lean_dec_ref_known(v_eq_x3f_5366_, 1);
v_ref_5368_ = lean_ctor_get(v___y_5364_, 2);
v___x_5369_ = l_Lean_SourceInfo_fromRef(v_ref_5368_, v___y_5353_);
v___x_5370_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5371_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5369_, 19);
v___x_5372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5369_);
lean_ctor_set(v___x_5372_, 1, v___x_5371_);
v___x_5373_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5374_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5369_);
lean_ctor_set(v___x_5375_, 1, v___x_5373_);
lean_ctor_set(v___x_5375_, 2, v___x_5374_);
v___x_5376_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5377_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5369_);
lean_ctor_set(v___x_5378_, 1, v___x_5377_);
v___x_5379_ = l_Lean_Syntax_node2(v___x_5369_, v___x_5373_, v_val_5367_, v___x_5378_);
v___x_5380_ = l_Lean_Syntax_node2(v___x_5369_, v___x_5376_, v___x_5379_, v___y_5356_);
v___x_5381_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5373_, v___x_5380_);
v___x_5382_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5369_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5386_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5369_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5373_, v___y_5354_);
v___x_5389_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5373_, v___x_5388_);
v___x_5390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5369_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
lean_inc_ref(v___x_5391_);
lean_inc_ref(v___x_5387_);
v___x_5392_ = l_Lean_Syntax_node4(v___x_5369_, v___x_5385_, v___x_5387_, v___x_5389_, v___x_5391_, v_body_5358_);
v___x_5393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5369_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
v___x_5396_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5393_, v___x_5395_);
v___x_5397_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5373_, v___x_5396_);
v___x_5398_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5373_, v___x_5397_);
v___x_5399_ = l_Lean_Syntax_node4(v___x_5369_, v___x_5385_, v___x_5387_, v___x_5398_, v___x_5391_, v___y_5357_);
v___x_5400_ = l_Lean_Syntax_node2(v___x_5369_, v___x_5373_, v___x_5392_, v___x_5399_);
v___x_5401_ = l_Lean_Syntax_node1(v___x_5369_, v___x_5384_, v___x_5400_);
lean_inc_ref_n(v___x_5375_, 2);
v___x_5402_ = l_Lean_Syntax_node7(v___x_5369_, v___x_5370_, v___x_5372_, v___x_5375_, v___x_5375_, v___x_5375_, v___x_5381_, v___x_5383_, v___x_5401_);
v___x_5403_ = l_Lean_Elab_Do_elabDoElem(v___x_5402_, v_dec_5340_, v___x_5350_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
return v___x_5403_;
}
else
{
lean_object* v_ref_5404_; lean_object* v___x_5405_; lean_object* v_a_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
lean_dec(v_eq_x3f_5366_);
v_ref_5404_ = lean_ctor_get(v___y_5364_, 2);
v___x_5405_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5404_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc_n(v_a_5406_, 18);
lean_dec_ref(v___x_5405_);
v___x_5407_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5408_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5409_, 0, v_a_5406_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5411_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5412_, 0, v_a_5406_);
lean_ctor_set(v___x_5412_, 1, v___x_5410_);
lean_ctor_set(v___x_5412_, 2, v___x_5411_);
v___x_5413_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5412_, 3);
v___x_5414_ = l_Lean_Syntax_node2(v_a_5406_, v___x_5413_, v___x_5412_, v___y_5356_);
v___x_5415_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5410_, v___x_5414_);
v___x_5416_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5417_, 0, v_a_5406_);
lean_ctor_set(v___x_5417_, 1, v___x_5416_);
v___x_5418_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5419_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5420_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5421_, 0, v_a_5406_);
lean_ctor_set(v___x_5421_, 1, v___x_5420_);
v___x_5422_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5410_, v___y_5354_);
v___x_5423_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5410_, v___x_5422_);
v___x_5424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5425_, 0, v_a_5406_);
lean_ctor_set(v___x_5425_, 1, v___x_5424_);
lean_inc_ref(v___x_5425_);
lean_inc_ref(v___x_5421_);
v___x_5426_ = l_Lean_Syntax_node4(v_a_5406_, v___x_5419_, v___x_5421_, v___x_5423_, v___x_5425_, v_body_5358_);
v___x_5427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5428_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5429_, 0, v_a_5406_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5427_, v___x_5429_);
v___x_5431_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5410_, v___x_5430_);
v___x_5432_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5410_, v___x_5431_);
v___x_5433_ = l_Lean_Syntax_node4(v_a_5406_, v___x_5419_, v___x_5421_, v___x_5432_, v___x_5425_, v___y_5357_);
v___x_5434_ = l_Lean_Syntax_node2(v_a_5406_, v___x_5410_, v___x_5426_, v___x_5433_);
v___x_5435_ = l_Lean_Syntax_node1(v_a_5406_, v___x_5418_, v___x_5434_);
v___x_5436_ = l_Lean_Syntax_node7(v_a_5406_, v___x_5407_, v___x_5409_, v___x_5412_, v___x_5412_, v___x_5412_, v___x_5415_, v___x_5417_, v___x_5435_);
v___x_5437_ = l_Lean_Elab_Do_elabDoElem(v___x_5436_, v_dec_5340_, v___x_5350_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
return v___x_5437_;
}
}
v___jp_5438_:
{
if (lean_obj_tag(v___y_5448_) == 0)
{
lean_dec_ref(v___y_5449_);
v___y_5353_ = v___y_5447_;
v___y_5354_ = v___y_5443_;
v___y_5355_ = v___y_5444_;
v___y_5356_ = v___y_5445_;
v___y_5357_ = v___y_5446_;
v_body_5358_ = v_a_5453_;
v___y_5359_ = v___y_5441_;
v___y_5360_ = v___y_5442_;
v___y_5361_ = v___y_5450_;
v___y_5362_ = v___y_5451_;
v___y_5363_ = v___y_5439_;
v___y_5364_ = v___y_5452_;
v___y_5365_ = v___y_5440_;
goto v___jp_5352_;
}
else
{
lean_dec_ref_known(v___y_5448_, 1);
if (v___x_5350_ == 0)
{
lean_dec_ref(v___y_5449_);
v___y_5353_ = v___y_5447_;
v___y_5354_ = v___y_5443_;
v___y_5355_ = v___y_5444_;
v___y_5356_ = v___y_5445_;
v___y_5357_ = v___y_5446_;
v_body_5358_ = v_a_5453_;
v___y_5359_ = v___y_5441_;
v___y_5360_ = v___y_5442_;
v___y_5361_ = v___y_5450_;
v___y_5362_ = v___y_5451_;
v___y_5363_ = v___y_5439_;
v___y_5364_ = v___y_5452_;
v___y_5365_ = v___y_5440_;
goto v___jp_5352_;
}
else
{
size_t v_sz_5454_; size_t v___x_5455_; lean_object* v___x_5456_; 
v_sz_5454_ = lean_array_size(v___y_5449_);
v___x_5455_ = ((size_t)0ULL);
v___x_5456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5449_, v_sz_5454_, v___x_5455_, v_a_5453_, v___y_5441_, v___y_5442_, v___y_5450_, v___y_5451_, v___y_5439_, v___y_5452_, v___y_5440_);
lean_dec_ref(v___y_5449_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v___y_5353_ = v___y_5447_;
v___y_5354_ = v___y_5443_;
v___y_5355_ = v___y_5444_;
v___y_5356_ = v___y_5445_;
v___y_5357_ = v___y_5446_;
v_body_5358_ = v_a_5457_;
v___y_5359_ = v___y_5441_;
v___y_5360_ = v___y_5442_;
v___y_5361_ = v___y_5450_;
v___y_5362_ = v___y_5451_;
v___y_5363_ = v___y_5439_;
v___y_5364_ = v___y_5452_;
v___y_5365_ = v___y_5440_;
goto v___jp_5352_;
}
else
{
lean_object* v_a_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5465_; 
lean_dec(v___y_5446_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v_dec_5340_);
v_a_5458_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5460_ = v___x_5456_;
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_a_5458_);
lean_dec(v___x_5456_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v___x_5463_; 
if (v_isShared_5461_ == 0)
{
v___x_5463_ = v___x_5460_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
}
}
v___jp_5466_:
{
uint8_t v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5480_ = 0;
v___x_5481_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5482_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5474_, v___y_5475_, v___x_5481_, v___y_5470_, v___y_5476_, v___y_5477_, v___y_5467_, v___y_5478_, v___y_5468_);
if (lean_obj_tag(v___x_5482_) == 0)
{
lean_object* v_a_5483_; lean_object* v___x_5484_; 
v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_a_5483_);
lean_dec_ref_known(v___x_5482_, 1);
v___x_5484_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5483_, v___y_5469_, v___y_5470_, v___y_5476_, v___y_5477_, v___y_5467_, v___y_5478_, v___y_5468_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v___x_5485_; 
lean_dec_ref_known(v___x_5484_, 1);
lean_inc(v___y_5471_);
v___x_5485_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5471_, v___y_5470_, v___y_5476_, v___y_5477_, v___y_5467_, v___y_5478_, v___y_5468_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
lean_inc(v___y_5475_);
v___x_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5487_, 0, v___y_5475_);
v___x_5488_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5487_, v_a_5486_, v___y_5469_, v___y_5470_, v___y_5476_, v___y_5477_, v___y_5467_, v___y_5478_, v___y_5468_);
lean_dec_ref_known(v___x_5487_, 1);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_dec_ref_known(v___x_5488_, 1);
if (lean_obj_tag(v___y_5479_) == 0)
{
lean_object* v_toCold_5489_; lean_object* v_ref_5490_; lean_object* v___x_5491_; lean_object* v_a_5492_; lean_object* v_quotContext_5493_; lean_object* v_currMacroScope_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; 
v_toCold_5489_ = lean_ctor_get(v___y_5478_, 0);
v_ref_5490_ = lean_ctor_get(v___y_5478_, 2);
v___x_5491_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5490_, v___y_5469_, v___y_5470_, v___y_5476_, v___y_5477_, v___y_5467_, v___y_5478_, v___y_5468_);
v_a_5492_ = lean_ctor_get(v___x_5491_, 0);
lean_inc_n(v_a_5492_, 9);
lean_dec_ref(v___x_5491_);
v_quotContext_5493_ = lean_ctor_get(v_toCold_5489_, 8);
v_currMacroScope_5494_ = lean_ctor_get(v_toCold_5489_, 9);
v___x_5495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5496_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5498_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5499_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5500_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5501_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5494_, 2);
lean_inc_n(v_quotContext_5493_, 2);
v___x_5502_ = l_Lean_addMacroScope(v_quotContext_5493_, v___x_5501_, v_currMacroScope_5494_);
v___x_5503_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5504_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5504_, 0, v_a_5492_);
lean_ctor_set(v___x_5504_, 1, v___x_5500_);
lean_ctor_set(v___x_5504_, 2, v___x_5502_);
lean_ctor_set(v___x_5504_, 3, v___x_5503_);
v___x_5505_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5506_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5507_ = l_Lean_addMacroScope(v_quotContext_5493_, v___x_5506_, v_currMacroScope_5494_);
v___x_5508_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5509_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5509_, 0, v_a_5492_);
lean_ctor_set(v___x_5509_, 1, v___x_5505_);
lean_ctor_set(v___x_5509_, 2, v___x_5507_);
lean_ctor_set(v___x_5509_, 3, v___x_5508_);
v___x_5510_ = l_Lean_Syntax_node1(v_a_5492_, v___x_5496_, v___x_5509_);
v___x_5511_ = l_Lean_Syntax_node2(v_a_5492_, v___x_5499_, v___x_5504_, v___x_5510_);
v___x_5512_ = l_Lean_Syntax_node1(v_a_5492_, v___x_5498_, v___x_5511_);
v___x_5513_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5514_, 0, v_a_5492_);
lean_ctor_set(v___x_5514_, 1, v___x_5496_);
lean_ctor_set(v___x_5514_, 2, v___x_5513_);
v___x_5515_ = l_Lean_Syntax_node2(v_a_5492_, v___x_5497_, v___x_5512_, v___x_5514_);
v___x_5516_ = l_Lean_Syntax_node1(v_a_5492_, v___x_5496_, v___x_5515_);
v___x_5517_ = l_Lean_Syntax_node1(v_a_5492_, v___x_5495_, v___x_5516_);
v___y_5439_ = v___y_5467_;
v___y_5440_ = v___y_5468_;
v___y_5441_ = v___y_5469_;
v___y_5442_ = v___y_5470_;
v___y_5443_ = v___y_5471_;
v___y_5444_ = v_a_5483_;
v___y_5445_ = v___y_5472_;
v___y_5446_ = v___y_5473_;
v___y_5447_ = v___x_5480_;
v___y_5448_ = v___y_5475_;
v___y_5449_ = v_a_5486_;
v___y_5450_ = v___y_5476_;
v___y_5451_ = v___y_5477_;
v___y_5452_ = v___y_5478_;
v_a_5453_ = v___x_5517_;
goto v___jp_5438_;
}
else
{
lean_object* v_val_5518_; 
v_val_5518_ = lean_ctor_get(v___y_5479_, 0);
lean_inc(v_val_5518_);
lean_dec_ref_known(v___y_5479_, 1);
v___y_5439_ = v___y_5467_;
v___y_5440_ = v___y_5468_;
v___y_5441_ = v___y_5469_;
v___y_5442_ = v___y_5470_;
v___y_5443_ = v___y_5471_;
v___y_5444_ = v_a_5483_;
v___y_5445_ = v___y_5472_;
v___y_5446_ = v___y_5473_;
v___y_5447_ = v___x_5480_;
v___y_5448_ = v___y_5475_;
v___y_5449_ = v_a_5486_;
v___y_5450_ = v___y_5476_;
v___y_5451_ = v___y_5477_;
v___y_5452_ = v___y_5478_;
v_a_5453_ = v_val_5518_;
goto v___jp_5438_;
}
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v_a_5486_);
lean_dec(v_a_5483_);
lean_dec(v___y_5479_);
lean_dec(v___y_5475_);
lean_dec(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v_dec_5340_);
v_a_5519_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5488_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5488_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_dec(v_a_5483_);
lean_dec(v___y_5479_);
lean_dec(v___y_5475_);
lean_dec(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v_dec_5340_);
v_a_5527_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5485_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5485_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_dec(v_a_5483_);
lean_dec(v___y_5479_);
lean_dec(v___y_5475_);
lean_dec(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v_dec_5340_);
v_a_5535_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5484_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5484_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
else
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
lean_dec(v___y_5479_);
lean_dec(v___y_5475_);
lean_dec(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v_dec_5340_);
v_a_5543_ = lean_ctor_get(v___x_5482_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5482_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5482_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5482_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5543_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
v___jp_5551_:
{
lean_object* v___x_5560_; lean_object* v_cfg_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; 
v___x_5560_ = lean_unsigned_to_nat(2u);
v_cfg_5561_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5560_);
v___x_5562_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5561_);
v___x_5563_ = l_Lean_Syntax_isOfKind(v_cfg_5561_, v___x_5562_);
if (v___x_5563_ == 0)
{
lean_object* v___x_5564_; 
lean_dec(v_cfg_5561_);
lean_dec(v_mutTk_x3f_5552_);
lean_dec_ref(v_dec_5340_);
lean_dec(v_stx_5339_);
v___x_5564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5564_;
}
else
{
lean_object* v___x_5565_; lean_object* v_pattern_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5565_ = lean_unsigned_to_nat(3u);
v_pattern_5566_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5565_);
v___x_5567_ = lean_unsigned_to_nat(5u);
v___x_5568_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5567_);
v___x_5569_ = lean_unsigned_to_nat(7u);
v___x_5570_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5569_);
v___x_5571_ = lean_unsigned_to_nat(8u);
v___x_5572_ = l_Lean_Syntax_getArg(v_stx_5339_, v___x_5571_);
lean_dec(v_stx_5339_);
v___x_5573_ = l_Lean_Syntax_getOptional_x3f(v___x_5572_);
lean_dec(v___x_5572_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_box(0);
v___y_5467_ = v___y_5557_;
v___y_5468_ = v___y_5559_;
v___y_5469_ = v___y_5553_;
v___y_5470_ = v___y_5554_;
v___y_5471_ = v_pattern_5566_;
v___y_5472_ = v___x_5568_;
v___y_5473_ = v___x_5570_;
v___y_5474_ = v_cfg_5561_;
v___y_5475_ = v_mutTk_x3f_5552_;
v___y_5476_ = v___y_5555_;
v___y_5477_ = v___y_5556_;
v___y_5478_ = v___y_5558_;
v___y_5479_ = v___x_5574_;
goto v___jp_5466_;
}
else
{
lean_object* v_val_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
v_val_5575_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5573_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_val_5575_);
lean_dec(v___x_5573_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_val_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
v___y_5467_ = v___y_5557_;
v___y_5468_ = v___y_5559_;
v___y_5469_ = v___y_5553_;
v___y_5470_ = v___y_5554_;
v___y_5471_ = v_pattern_5566_;
v___y_5472_ = v___x_5568_;
v___y_5473_ = v___x_5570_;
v___y_5474_ = v_cfg_5561_;
v___y_5475_ = v_mutTk_x3f_5552_;
v___y_5476_ = v___y_5555_;
v___y_5477_ = v___y_5556_;
v___y_5478_ = v___y_5558_;
v___y_5479_ = v___x_5580_;
goto v___jp_5466_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5592_, lean_object* v_dec_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5592_, v_dec_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_);
lean_dec(v_a_5600_);
lean_dec_ref(v_a_5599_);
lean_dec(v_a_5598_);
lean_dec_ref(v_a_5597_);
lean_dec(v_a_5596_);
lean_dec_ref(v_a_5595_);
lean_dec_ref(v_a_5594_);
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5603_, size_t v_sz_5604_, size_t v_i_5605_, lean_object* v_b_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_){
_start:
{
lean_object* v___x_5615_; 
v___x_5615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5603_, v_sz_5604_, v_i_5605_, v_b_5606_, v___y_5612_);
return v___x_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5616_, lean_object* v_sz_5617_, lean_object* v_i_5618_, lean_object* v_b_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
size_t v_sz_boxed_5628_; size_t v_i_boxed_5629_; lean_object* v_res_5630_; 
v_sz_boxed_5628_ = lean_unbox_usize(v_sz_5617_);
lean_dec(v_sz_5617_);
v_i_boxed_5629_ = lean_unbox_usize(v_i_5618_);
lean_dec(v_i_5618_);
v_res_5630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5616_, v_sz_boxed_5628_, v_i_boxed_5629_, v_b_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec_ref(v_as_5616_);
return v_res_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5638_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5639_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5640_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5641_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5642_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5638_, v___x_5639_, v___x_5640_, v___x_5641_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5644_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5652_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5653_ = l_Lean_stringToMessageData(v___x_5652_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5654_, lean_object* v_dec_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_){
_start:
{
lean_object* v___x_5664_; uint8_t v___x_5665_; 
v___x_5664_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5654_);
v___x_5665_ = l_Lean_Syntax_isOfKind(v_stx_5654_, v___x_5664_);
if (v___x_5665_ == 0)
{
lean_object* v___x_5666_; 
lean_dec_ref(v_dec_5655_);
lean_dec(v_stx_5654_);
v___x_5666_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5666_;
}
else
{
lean_object* v___x_5667_; lean_object* v_tk_5668_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5674_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v___y_5677_; lean_object* v___y_5678_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v___y_5707_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; uint8_t v___y_5714_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; uint8_t v___y_5728_; lean_object* v_mutTk_x3f_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___x_5768_; lean_object* v___x_5769_; uint8_t v___x_5770_; 
v___x_5667_ = lean_unsigned_to_nat(0u);
v_tk_5668_ = l_Lean_Syntax_getArg(v_stx_5654_, v___x_5667_);
v___x_5768_ = lean_unsigned_to_nat(1u);
v___x_5769_ = l_Lean_Syntax_getArg(v_stx_5654_, v___x_5768_);
v___x_5770_ = l_Lean_Syntax_isNone(v___x_5769_);
if (v___x_5770_ == 0)
{
uint8_t v___x_5771_; 
lean_inc(v___x_5769_);
v___x_5771_ = l_Lean_Syntax_matchesNull(v___x_5769_, v___x_5768_);
if (v___x_5771_ == 0)
{
lean_object* v___x_5772_; 
lean_dec(v___x_5769_);
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
lean_dec(v_stx_5654_);
v___x_5772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5772_;
}
else
{
lean_object* v_mutTk_x3f_5773_; lean_object* v___x_5774_; 
v_mutTk_x3f_5773_ = l_Lean_Syntax_getArg(v___x_5769_, v___x_5667_);
lean_dec(v___x_5769_);
v___x_5774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5774_, 0, v_mutTk_x3f_5773_);
v_mutTk_x3f_5731_ = v___x_5774_;
v___y_5732_ = v_a_5656_;
v___y_5733_ = v_a_5657_;
v___y_5734_ = v_a_5658_;
v___y_5735_ = v_a_5659_;
v___y_5736_ = v_a_5660_;
v___y_5737_ = v_a_5661_;
v___y_5738_ = v_a_5662_;
goto v___jp_5730_;
}
}
else
{
lean_object* v___x_5775_; 
lean_dec(v___x_5769_);
v___x_5775_ = lean_box(0);
v_mutTk_x3f_5731_ = v___x_5775_;
v___y_5732_ = v_a_5656_;
v___y_5733_ = v_a_5657_;
v___y_5734_ = v_a_5658_;
v___y_5735_ = v_a_5659_;
v___y_5736_ = v_a_5660_;
v___y_5737_ = v_a_5661_;
v___y_5738_ = v_a_5662_;
goto v___jp_5730_;
}
v___jp_5669_:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5679_, 0, v___y_5671_);
v___x_5680_ = l_Lean_Elab_Do_elabDoArrow(v___x_5679_, v___y_5670_, v_tk_5668_, v_dec_5655_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_);
lean_dec(v_tk_5668_);
return v___x_5680_;
}
v___jp_5681_:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_dec(v___y_5688_);
lean_dec(v___y_5684_);
v___x_5692_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5693_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5683_, v___x_5692_, v___y_5682_, v___y_5686_, v___y_5691_, v___y_5687_);
lean_dec(v___y_5683_);
v_a_5694_ = lean_ctor_get(v___x_5693_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5693_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5693_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5693_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
v___jp_5702_:
{
if (v___y_5714_ == 0)
{
lean_object* v_eq_x3f_5715_; 
v_eq_x3f_5715_ = lean_ctor_get(v___y_5705_, 0);
lean_inc(v_eq_x3f_5715_);
lean_dec_ref(v___y_5705_);
if (lean_obj_tag(v_eq_x3f_5715_) == 0)
{
lean_dec(v___y_5703_);
v___y_5670_ = v___y_5706_;
v___y_5671_ = v___y_5710_;
v___y_5672_ = v___y_5712_;
v___y_5673_ = v___y_5711_;
v___y_5674_ = v___y_5707_;
v___y_5675_ = v___y_5704_;
v___y_5676_ = v___y_5708_;
v___y_5677_ = v___y_5713_;
v___y_5678_ = v___y_5709_;
goto v___jp_5669_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5715_, 1);
if (v___x_5665_ == 0)
{
lean_dec(v___y_5703_);
v___y_5670_ = v___y_5706_;
v___y_5671_ = v___y_5710_;
v___y_5672_ = v___y_5712_;
v___y_5673_ = v___y_5711_;
v___y_5674_ = v___y_5707_;
v___y_5675_ = v___y_5704_;
v___y_5676_ = v___y_5708_;
v___y_5677_ = v___y_5713_;
v___y_5678_ = v___y_5709_;
goto v___jp_5669_;
}
else
{
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
v___y_5682_ = v___y_5704_;
v___y_5683_ = v___y_5703_;
v___y_5684_ = v___y_5706_;
v___y_5685_ = v___y_5707_;
v___y_5686_ = v___y_5708_;
v___y_5687_ = v___y_5709_;
v___y_5688_ = v___y_5710_;
v___y_5689_ = v___y_5711_;
v___y_5690_ = v___y_5712_;
v___y_5691_ = v___y_5713_;
goto v___jp_5681_;
}
}
}
else
{
lean_dec_ref(v___y_5705_);
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
v___y_5682_ = v___y_5704_;
v___y_5683_ = v___y_5703_;
v___y_5684_ = v___y_5706_;
v___y_5685_ = v___y_5707_;
v___y_5686_ = v___y_5708_;
v___y_5687_ = v___y_5709_;
v___y_5688_ = v___y_5710_;
v___y_5689_ = v___y_5711_;
v___y_5690_ = v___y_5712_;
v___y_5691_ = v___y_5713_;
goto v___jp_5681_;
}
}
v___jp_5716_:
{
if (v___y_5728_ == 0)
{
uint8_t v_zeta_5729_; 
v_zeta_5729_ = lean_ctor_get_uint8(v___y_5719_, sizeof(void*)*1 + 2);
v___y_5703_ = v___y_5718_;
v___y_5704_ = v___y_5717_;
v___y_5705_ = v___y_5719_;
v___y_5706_ = v___y_5721_;
v___y_5707_ = v___y_5720_;
v___y_5708_ = v___y_5722_;
v___y_5709_ = v___y_5723_;
v___y_5710_ = v___y_5726_;
v___y_5711_ = v___y_5725_;
v___y_5712_ = v___y_5724_;
v___y_5713_ = v___y_5727_;
v___y_5714_ = v_zeta_5729_;
goto v___jp_5702_;
}
else
{
v___y_5703_ = v___y_5718_;
v___y_5704_ = v___y_5717_;
v___y_5705_ = v___y_5719_;
v___y_5706_ = v___y_5721_;
v___y_5707_ = v___y_5720_;
v___y_5708_ = v___y_5722_;
v___y_5709_ = v___y_5723_;
v___y_5710_ = v___y_5726_;
v___y_5711_ = v___y_5725_;
v___y_5712_ = v___y_5724_;
v___y_5713_ = v___y_5727_;
v___y_5714_ = v___x_5665_;
goto v___jp_5702_;
}
}
v___jp_5730_:
{
lean_object* v___x_5739_; lean_object* v_cfg_5740_; lean_object* v___x_5741_; uint8_t v___x_5742_; 
v___x_5739_ = lean_unsigned_to_nat(2u);
v_cfg_5740_ = l_Lean_Syntax_getArg(v_stx_5654_, v___x_5739_);
v___x_5741_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5740_);
v___x_5742_ = l_Lean_Syntax_isOfKind(v_cfg_5740_, v___x_5741_);
if (v___x_5742_ == 0)
{
lean_object* v___x_5743_; 
lean_dec(v_cfg_5740_);
lean_dec(v_mutTk_x3f_5731_);
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
lean_dec(v_stx_5654_);
v___x_5743_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5743_;
}
else
{
lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5744_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5740_);
v___x_5745_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5740_, v_mutTk_x3f_5731_, v___x_5744_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
lean_inc(v_a_5746_);
lean_dec_ref_known(v___x_5745_, 1);
v___x_5747_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5746_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
if (lean_obj_tag(v___x_5747_) == 0)
{
uint8_t v_nondep_5748_; uint8_t v_usedOnly_5749_; lean_object* v___x_5750_; lean_object* v_decl_5751_; 
lean_dec_ref_known(v___x_5747_, 1);
v_nondep_5748_ = lean_ctor_get_uint8(v_a_5746_, sizeof(void*)*1);
v_usedOnly_5749_ = lean_ctor_get_uint8(v_a_5746_, sizeof(void*)*1 + 1);
v___x_5750_ = lean_unsigned_to_nat(3u);
v_decl_5751_ = l_Lean_Syntax_getArg(v_stx_5654_, v___x_5750_);
lean_dec(v_stx_5654_);
if (v_nondep_5748_ == 0)
{
v___y_5717_ = v___y_5735_;
v___y_5718_ = v_cfg_5740_;
v___y_5719_ = v_a_5746_;
v___y_5720_ = v___y_5734_;
v___y_5721_ = v_decl_5751_;
v___y_5722_ = v___y_5736_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5732_;
v___y_5725_ = v___y_5733_;
v___y_5726_ = v_mutTk_x3f_5731_;
v___y_5727_ = v___y_5737_;
v___y_5728_ = v_usedOnly_5749_;
goto v___jp_5716_;
}
else
{
v___y_5717_ = v___y_5735_;
v___y_5718_ = v_cfg_5740_;
v___y_5719_ = v_a_5746_;
v___y_5720_ = v___y_5734_;
v___y_5721_ = v_decl_5751_;
v___y_5722_ = v___y_5736_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5732_;
v___y_5725_ = v___y_5733_;
v___y_5726_ = v_mutTk_x3f_5731_;
v___y_5727_ = v___y_5737_;
v___y_5728_ = v___x_5665_;
goto v___jp_5716_;
}
}
else
{
lean_object* v_a_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5759_; 
lean_dec(v_a_5746_);
lean_dec(v_cfg_5740_);
lean_dec(v_mutTk_x3f_5731_);
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
lean_dec(v_stx_5654_);
v_a_5752_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5754_ = v___x_5747_;
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5747_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5757_; 
if (v_isShared_5755_ == 0)
{
v___x_5757_ = v___x_5754_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
}
else
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5767_; 
lean_dec(v_cfg_5740_);
lean_dec(v_mutTk_x3f_5731_);
lean_dec(v_tk_5668_);
lean_dec_ref(v_dec_5655_);
lean_dec(v_stx_5654_);
v_a_5760_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5767_ == 0)
{
v___x_5762_ = v___x_5745_;
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5745_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5765_; 
if (v_isShared_5763_ == 0)
{
v___x_5765_ = v___x_5762_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5776_, lean_object* v_dec_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_){
_start:
{
lean_object* v_res_5786_; 
v_res_5786_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5776_, v_dec_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_);
lean_dec(v_a_5784_);
lean_dec_ref(v_a_5783_);
lean_dec(v_a_5782_);
lean_dec_ref(v_a_5781_);
lean_dec(v_a_5780_);
lean_dec_ref(v_a_5779_);
lean_dec_ref(v_a_5778_);
return v_res_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5794_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5795_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5796_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5797_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5798_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5794_, v___x_5795_, v___x_5796_, v___x_5797_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5807_, lean_object* v_dec_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_){
_start:
{
lean_object* v___x_5817_; uint8_t v___x_5818_; 
v___x_5817_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5807_);
v___x_5818_ = l_Lean_Syntax_isOfKind(v_stx_5807_, v___x_5817_);
if (v___x_5818_ == 0)
{
lean_object* v___x_5819_; 
lean_dec_ref(v_dec_5808_);
lean_dec(v_stx_5807_);
v___x_5819_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5819_;
}
else
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; uint8_t v___x_5823_; 
v___x_5820_ = lean_unsigned_to_nat(0u);
v___x_5821_ = l_Lean_Syntax_getArg(v_stx_5807_, v___x_5820_);
lean_dec(v_stx_5807_);
v___x_5822_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5821_);
v___x_5823_ = l_Lean_Syntax_isOfKind(v___x_5821_, v___x_5822_);
if (v___x_5823_ == 0)
{
lean_object* v___x_5824_; uint8_t v___x_5825_; 
v___x_5824_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5821_);
v___x_5825_ = l_Lean_Syntax_isOfKind(v___x_5821_, v___x_5824_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; 
lean_dec(v___x_5821_);
lean_dec_ref(v_dec_5808_);
v___x_5826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5826_;
}
else
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = lean_box(2);
lean_inc(v___x_5821_);
v___x_5828_ = l_Lean_Elab_Do_elabDoArrow(v___x_5827_, v___x_5821_, v___x_5821_, v_dec_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
lean_dec(v___x_5821_);
return v___x_5828_;
}
}
else
{
lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5829_ = lean_box(2);
lean_inc(v___x_5821_);
v___x_5830_ = l_Lean_Elab_Do_elabDoArrow(v___x_5829_, v___x_5821_, v___x_5821_, v_dec_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
lean_dec(v___x_5821_);
return v___x_5830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5831_, lean_object* v_dec_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_){
_start:
{
lean_object* v_res_5841_; 
v_res_5841_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5831_, v_dec_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_);
lean_dec(v_a_5839_);
lean_dec_ref(v_a_5838_);
lean_dec(v_a_5837_);
lean_dec_ref(v_a_5836_);
lean_dec(v_a_5835_);
lean_dec_ref(v_a_5834_);
lean_dec_ref(v_a_5833_);
return v_res_5841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5849_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5850_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5851_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5852_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5853_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5849_, v___x_5850_, v___x_5851_, v___x_5852_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5855_;
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
