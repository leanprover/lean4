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
v_options_309_ = lean_ctor_get(v___y_301_, 1);
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
v_options_376_ = lean_ctor_get(v___y_374_, 1);
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
v_ref_412_ = lean_ctor_get(v___y_409_, 4);
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
lean_object* v___x_549_; lean_object* v___y_551_; lean_object* v_pattern_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___x_622_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_546_);
v___x_622_ = l_Lean_Syntax_isOfKind(v___x_546_, v___x_549_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_546_);
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_624_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_625_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = l_Lean_Syntax_getArg(v___x_546_, v___x_627_);
v___x_629_ = l_Lean_Syntax_matchesNull(v___x_628_, v___x_545_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_546_);
v___x_630_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_631_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_632_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_633_;
}
else
{
lean_object* v_pattern_634_; lean_object* v_xType_x3f_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_pattern_634_ = l_Lean_Syntax_getArg(v___x_546_, v___x_545_);
v___x_670_ = lean_unsigned_to_nat(2u);
v___x_671_ = l_Lean_Syntax_getArg(v___x_546_, v___x_670_);
v___x_672_ = l_Lean_Syntax_isNone(v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
lean_inc(v___x_671_);
v___x_673_ = l_Lean_Syntax_matchesNull(v___x_671_, v___x_627_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_671_);
lean_dec(v_pattern_634_);
lean_dec(v___x_546_);
v___x_674_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_675_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_676_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = l_Lean_Syntax_getArg(v___x_671_, v___x_545_);
lean_dec(v___x_671_);
v___x_679_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_678_);
v___x_680_ = l_Lean_Syntax_isOfKind(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_678_);
lean_dec(v_pattern_634_);
lean_dec(v___x_546_);
v___x_681_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_682_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_683_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_684_;
}
else
{
lean_object* v_xType_x3f_685_; lean_object* v___x_686_; 
lean_dec(v_decl_531_);
v_xType_x3f_685_ = l_Lean_Syntax_getArg(v___x_678_, v___x_627_);
lean_dec(v___x_678_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_xType_x3f_685_);
v_xType_x3f_636_ = v___x_686_;
v___y_637_ = v_a_532_;
v___y_638_ = v_a_533_;
v___y_639_ = v_a_534_;
v___y_640_ = v_a_535_;
v___y_641_ = v_a_536_;
v___y_642_ = v_a_537_;
goto v___jp_635_;
}
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v___x_671_);
lean_dec(v_decl_531_);
v___x_687_ = lean_box(0);
v_xType_x3f_636_ = v___x_687_;
v___y_637_ = v_a_532_;
v___y_638_ = v_a_533_;
v___y_639_ = v_a_534_;
v___y_640_ = v_a_535_;
v___y_641_ = v_a_536_;
v___y_642_ = v_a_537_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = l_Lean_Syntax_getArg(v___x_546_, v___x_643_);
lean_dec(v___x_546_);
if (lean_obj_tag(v_xType_x3f_636_) == 0)
{
v___y_551_ = v___x_644_;
v_pattern_552_ = v_pattern_634_;
v___y_553_ = v___y_637_;
v___y_554_ = v___y_638_;
v___y_555_ = v___y_639_;
v___y_556_ = v___y_640_;
v___y_557_ = v___y_641_;
v___y_558_ = v___y_642_;
goto v___jp_550_;
}
else
{
lean_object* v_toCold_645_; lean_object* v_val_646_; lean_object* v_ref_647_; lean_object* v_currMacroScope_648_; lean_object* v_quotContext_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_toCold_645_ = lean_ctor_get(v___y_641_, 0);
v_val_646_ = lean_ctor_get(v_xType_x3f_636_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_xType_x3f_636_, 1);
v_ref_647_ = lean_ctor_get(v___y_641_, 4);
v_currMacroScope_648_ = lean_ctor_get(v___y_641_, 9);
v_quotContext_649_ = lean_ctor_get(v_toCold_645_, 2);
v___x_650_ = l_Lean_SourceInfo_fromRef(v_ref_647_, v___x_548_);
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_650_, 7);
v___x_654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_650_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_656_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_657_ = lean_box(0);
lean_inc(v_currMacroScope_648_);
lean_inc(v_quotContext_649_);
v___x_658_ = l_Lean_addMacroScope(v_quotContext_649_, v___x_657_, v_currMacroScope_648_);
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_660_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_660_, 0, v___x_650_);
lean_ctor_set(v___x_660_, 1, v___x_656_);
lean_ctor_set(v___x_660_, 2, v___x_658_);
lean_ctor_set(v___x_660_, 3, v___x_659_);
v___x_661_ = l_Lean_Syntax_node1(v___x_650_, v___x_655_, v___x_660_);
v___x_662_ = l_Lean_Syntax_node2(v___x_650_, v___x_652_, v___x_654_, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_650_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_666_ = l_Lean_Syntax_node1(v___x_650_, v___x_665_, v_val_646_);
v___x_667_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_650_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_Syntax_node5(v___x_650_, v___x_651_, v___x_662_, v_pattern_634_, v___x_664_, v___x_666_, v___x_668_);
v___y_551_ = v___x_644_;
v_pattern_552_ = v___x_669_;
v___y_553_ = v___y_637_;
v___y_554_ = v___y_638_;
v___y_555_ = v___y_639_;
v___y_556_ = v___y_640_;
v___y_557_ = v___y_641_;
v___y_558_ = v___y_642_;
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
lean_object* v_toCold_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_605_; 
v_toCold_568_ = lean_ctor_get(v___y_557_, 0);
v_a_569_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_605_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_ref_573_; lean_object* v_currMacroScope_574_; lean_object* v_quotContext_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_ref_573_ = lean_ctor_get(v___y_557_, 4);
v_currMacroScope_574_ = lean_ctor_get(v___y_557_, 9);
v_quotContext_575_ = lean_ctor_get(v_toCold_568_, 2);
v___x_576_ = l_Lean_SourceInfo_fromRef(v_ref_573_, v___x_548_);
v___x_577_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_578_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_576_, 11);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_576_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_583_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_576_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_587_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_588_ = lean_box(0);
lean_inc(v_currMacroScope_574_);
lean_inc(v_quotContext_575_);
v___x_589_ = l_Lean_addMacroScope(v_quotContext_575_, v___x_588_, v_currMacroScope_574_);
v___x_590_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_591_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_591_, 0, v___x_576_);
lean_ctor_set(v___x_591_, 1, v___x_587_);
lean_ctor_set(v___x_591_, 2, v___x_589_);
lean_ctor_set(v___x_591_, 3, v___x_590_);
v___x_592_ = l_Lean_Syntax_node1(v___x_576_, v___x_586_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node2(v___x_576_, v___x_583_, v___x_585_, v___x_592_);
v___x_594_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_576_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Syntax_node1(v___x_576_, v___x_577_, v_a_569_);
v___x_597_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_576_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_Syntax_node5(v___x_576_, v___x_582_, v___x_593_, v___y_551_, v___x_595_, v___x_596_, v___x_598_);
lean_inc_ref(v___x_579_);
v___x_600_ = l_Lean_Syntax_node5(v___x_576_, v___x_549_, v_pattern_552_, v___x_579_, v___x_579_, v___x_581_, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v___x_576_, v___x_539_, v___x_600_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_601_);
v___x_603_ = v___x_571_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
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
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_pattern_552_);
lean_dec(v___y_551_);
v_a_606_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_565_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_565_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_pattern_552_);
lean_dec(v___y_551_);
v_a_614_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_563_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_563_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = l_Lean_Syntax_getArg(v___x_546_, v___x_545_);
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_688_);
v___x_690_ = l_Lean_Syntax_isOfKind(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_688_);
lean_dec(v___x_546_);
v___x_691_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_692_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_693_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_694_;
}
else
{
lean_object* v_x_695_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v_a_704_; lean_object* v_xType_x3f_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_x_695_ = l_Lean_Syntax_getArg(v___x_688_, v___x_545_);
lean_dec(v___x_688_);
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_695_);
v___x_782_ = l_Lean_Syntax_isOfKind(v_x_695_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_x_695_);
lean_dec(v___x_546_);
v___x_783_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_784_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_785_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = l_Lean_Syntax_getArg(v___x_546_, v___x_787_);
v___x_789_ = l_Lean_Syntax_matchesNull(v___x_788_, v___x_545_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_x_695_);
lean_dec(v___x_546_);
v___x_790_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_791_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_792_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(2u);
v___x_795_ = l_Lean_Syntax_getArg(v___x_546_, v___x_794_);
v___x_796_ = l_Lean_Syntax_isNone(v___x_795_);
if (v___x_796_ == 0)
{
uint8_t v___x_797_; 
lean_inc(v___x_795_);
v___x_797_ = l_Lean_Syntax_matchesNull(v___x_795_, v___x_787_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v___x_795_);
lean_dec(v_x_695_);
lean_dec(v___x_546_);
v___x_798_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_799_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_800_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = l_Lean_Syntax_getArg(v___x_795_, v___x_545_);
lean_dec(v___x_795_);
v___x_803_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_802_);
v___x_804_ = l_Lean_Syntax_isOfKind(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_802_);
lean_dec(v_x_695_);
lean_dec(v___x_546_);
v___x_805_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_806_ = l_Lean_MessageData_ofSyntax(v_decl_531_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_807_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_808_;
}
else
{
lean_object* v_xType_x3f_809_; lean_object* v___x_810_; 
lean_dec(v_decl_531_);
v_xType_x3f_809_ = l_Lean_Syntax_getArg(v___x_802_, v___x_787_);
lean_dec(v___x_802_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v_xType_x3f_809_);
v_xType_x3f_753_ = v___x_810_;
v___y_754_ = v_a_532_;
v___y_755_ = v_a_533_;
v___y_756_ = v_a_534_;
v___y_757_ = v_a_535_;
v___y_758_ = v_a_536_;
v___y_759_ = v_a_537_;
goto v___jp_752_;
}
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v___x_795_);
lean_dec(v_decl_531_);
v___x_811_ = lean_box(0);
v_xType_x3f_753_ = v___x_811_;
v___y_754_ = v_a_532_;
v___y_755_ = v_a_533_;
v___y_756_ = v_a_534_;
v___y_757_ = v_a_535_;
v___y_758_ = v_a_536_;
v___y_759_ = v_a_537_;
goto v___jp_752_;
}
}
}
v___jp_696_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
lean_inc(v_x_695_);
v___x_706_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_695_, v_a_704_, v___x_540_, v___x_540_, v___x_705_, v___y_698_, v___y_703_, v___y_701_, v___y_702_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref_known(v___x_706_, 1);
v___x_707_ = l_Lean_TSyntax_getId(v_x_695_);
v___x_708_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_707_, v___y_701_, v___y_702_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Lean_LocalDecl_type(v_a_709_);
lean_dec(v_a_709_);
v___x_711_ = l_Lean_Elab_Term_exprToSyntax(v___x_710_, v___y_698_, v___y_703_, v___y_701_, v___y_702_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_735_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_735_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_735_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_735_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_ref_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_ref_716_ = lean_ctor_get(v___y_699_, 4);
v___x_717_ = 0;
v___x_718_ = l_Lean_SourceInfo_fromRef(v_ref_716_, v___x_717_);
lean_inc_n(v___x_718_, 7);
v___x_719_ = l_Lean_Syntax_node1(v___x_718_, v___x_689_, v_x_695_);
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v___x_718_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_718_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_Syntax_node2(v___x_718_, v___x_723_, v___x_725_, v_a_712_);
v___x_727_ = l_Lean_Syntax_node1(v___x_718_, v___x_720_, v___x_726_);
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_718_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_Syntax_node5(v___x_718_, v___x_547_, v___x_719_, v___x_722_, v___x_727_, v___x_729_, v___y_697_);
v___x_731_ = l_Lean_Syntax_node1(v___x_718_, v___x_539_, v___x_730_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_731_);
v___x_733_ = v___x_714_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_dec(v___y_697_);
lean_dec(v_x_695_);
return v___x_711_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v___y_697_);
lean_dec(v_x_695_);
v_a_736_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_708_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_708_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v___y_697_);
lean_dec(v_x_695_);
v_a_744_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_706_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_706_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
v___jp_752_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(4u);
v___x_761_ = l_Lean_Syntax_getArg(v___x_546_, v___x_760_);
lean_dec(v___x_546_);
if (lean_obj_tag(v_xType_x3f_753_) == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_box(0);
v___y_697_ = v___x_761_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_758_;
v___y_700_ = v___y_759_;
v___y_701_ = v___y_756_;
v___y_702_ = v___y_757_;
v___y_703_ = v___y_755_;
v_a_704_ = v___x_762_;
goto v___jp_696_;
}
else
{
lean_object* v_val_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_780_; 
v_val_763_ = lean_ctor_get(v_xType_x3f_753_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_xType_x3f_753_);
if (v_isSharedCheck_780_ == 0)
{
v___x_765_ = v_xType_x3f_753_;
v_isShared_766_ = v_isSharedCheck_780_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_val_763_);
lean_dec(v_xType_x3f_753_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_780_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Elab_Term_elabType(v_val_763_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_a_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v___y_697_ = v___x_761_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_758_;
v___y_700_ = v___y_759_;
v___y_701_ = v___y_756_;
v___y_702_ = v___y_757_;
v___y_703_ = v___y_755_;
v_a_704_ = v___x_770_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_765_);
lean_dec(v___x_761_);
lean_dec(v_x_695_);
v_a_772_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_767_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
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
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_decl_531_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_813_, lean_object* v_decl_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_813_, v_decl_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_letOrReassign_813_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_833_, lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_833_, v_msg_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_843_, lean_object* v_macroStack_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_843_, v_macroStack_844_, v___y_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_853_, lean_object* v_macroStack_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_853_, v_macroStack_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_ref_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_ref_869_ = lean_ctor_get(v___y_866_, 4);
v___x_870_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_inc(v_ref_869_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_ref_869_);
lean_ctor_set(v___x_875_, 1, v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 1);
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_886_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
uint8_t v_postponeValue_902_; uint8_t v_generalize_903_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; 
v_postponeValue_902_ = lean_ctor_get_uint8(v_config_893_, sizeof(void*)*1 + 3);
v_generalize_903_ = lean_ctor_get_uint8(v_config_893_, sizeof(void*)*1 + 4);
if (v_postponeValue_902_ == 0)
{
v___y_905_ = v_a_894_;
v___y_906_ = v_a_895_;
v___y_907_ = v_a_896_;
v___y_908_ = v_a_897_;
v___y_909_ = v_a_898_;
v___y_910_ = v_a_899_;
v___y_911_ = v_a_900_;
goto v___jp_904_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_917_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_916_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_917_;
}
v___jp_904_:
{
if (v_generalize_903_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_915_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_914_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec_ref(v_config_918_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_928_, lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_929_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_939_, lean_object* v_msg_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_939_, v_msg_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_949_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
v___x_951_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_978_, lean_object* v_x_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_keyedConfig_987_; uint8_t v_trackZetaDelta_988_; lean_object* v_zetaDeltaSet_989_; lean_object* v_localInstances_990_; lean_object* v_defEqCtx_x3f_991_; lean_object* v_synthPendingDepth_992_; lean_object* v_customCanUnfoldPredicate_x3f_993_; uint8_t v_univApprox_994_; uint8_t v_inTypeClassResolution_995_; uint8_t v_cacheInferType_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_keyedConfig_987_ = lean_ctor_get(v___y_982_, 0);
v_trackZetaDelta_988_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*7);
v_zetaDeltaSet_989_ = lean_ctor_get(v___y_982_, 1);
v_localInstances_990_ = lean_ctor_get(v___y_982_, 3);
v_defEqCtx_x3f_991_ = lean_ctor_get(v___y_982_, 4);
v_synthPendingDepth_992_ = lean_ctor_get(v___y_982_, 5);
v_customCanUnfoldPredicate_x3f_993_ = lean_ctor_get(v___y_982_, 6);
v_univApprox_994_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_995_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*7 + 2);
v_cacheInferType_996_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_993_);
lean_inc(v_synthPendingDepth_992_);
lean_inc(v_defEqCtx_x3f_991_);
lean_inc_ref(v_localInstances_990_);
lean_inc(v_zetaDeltaSet_989_);
lean_inc_ref(v_keyedConfig_987_);
v___x_997_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_997_, 0, v_keyedConfig_987_);
lean_ctor_set(v___x_997_, 1, v_zetaDeltaSet_989_);
lean_ctor_set(v___x_997_, 2, v_lctx_978_);
lean_ctor_set(v___x_997_, 3, v_localInstances_990_);
lean_ctor_set(v___x_997_, 4, v_defEqCtx_x3f_991_);
lean_ctor_set(v___x_997_, 5, v_synthPendingDepth_992_);
lean_ctor_set(v___x_997_, 6, v_customCanUnfoldPredicate_x3f_993_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*7, v_trackZetaDelta_988_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*7 + 1, v_univApprox_994_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*7 + 2, v_inTypeClassResolution_995_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*7 + 3, v_cacheInferType_996_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_998_ = lean_apply_7(v_x_979_, v___y_980_, v___y_981_, v___x_997_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1017_, lean_object* v_lctx_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_lctx_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1028_, v_lctx_1029_, v_x_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc_ref(v___y_1040_);
v___x_1049_ = lean_apply_9(v_k_1039_, v_b_1043_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1061_, lean_object* v_type_1062_, lean_object* v_val_1063_, lean_object* v_k_1064_, uint8_t v_nondep_1065_, uint8_t v_kind_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; 
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc_ref(v___y_1067_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1075_, 0, v_k_1064_);
lean_closure_set(v___f_1075_, 1, v___y_1067_);
lean_closure_set(v___f_1075_, 2, v___y_1068_);
lean_closure_set(v___f_1075_, 3, v___y_1069_);
v___x_1076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1061_, v_type_1062_, v_val_1063_, v___f_1075_, v_nondep_1065_, v_kind_1066_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1076_) == 0)
{
return v___x_1076_;
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1085_, lean_object* v_type_1086_, lean_object* v_val_1087_, lean_object* v_k_1088_, lean_object* v_nondep_1089_, lean_object* v_kind_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v_nondep_boxed_1099_; uint8_t v_kind_boxed_1100_; lean_object* v_res_1101_; 
v_nondep_boxed_1099_ = lean_unbox(v_nondep_1089_);
v_kind_boxed_1100_ = lean_unbox(v_kind_1090_);
v_res_1101_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1085_, v_type_1086_, v_val_1087_, v_k_1088_, v_nondep_boxed_1099_, v_kind_boxed_1100_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1102_, lean_object* v_name_1103_, lean_object* v_type_1104_, lean_object* v_val_1105_, lean_object* v_k_1106_, uint8_t v_nondep_1107_, uint8_t v_kind_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1103_, v_type_1104_, v_val_1105_, v_k_1106_, v_nondep_1107_, v_kind_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_name_1119_, lean_object* v_type_1120_, lean_object* v_val_1121_, lean_object* v_k_1122_, lean_object* v_nondep_1123_, lean_object* v_kind_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_nondep_boxed_1133_; uint8_t v_kind_boxed_1134_; lean_object* v_res_1135_; 
v_nondep_boxed_1133_ = lean_unbox(v_nondep_1123_);
v_kind_boxed_1134_ = lean_unbox(v_kind_1124_);
v_res_1135_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1118_, v_name_1119_, v_type_1120_, v_val_1121_, v_k_1122_, v_nondep_boxed_1133_, v_kind_boxed_1134_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1136_, lean_object* v___x_1137_, uint8_t v___x_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, uint8_t v___x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1136_, v___x_1137_, v___x_1138_, v___x_1138_, v___x_1139_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = 1;
v___x_1152_ = l_Lean_Meta_mkLambdaFVars(v___x_1140_, v_a_1150_, v___x_1141_, v___x_1141_, v___x_1141_, v___x_1138_, v___x_1151_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1152_;
}
else
{
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v___x_86070__boxed_1166_; uint8_t v___x_86073__boxed_1167_; lean_object* v_res_1168_; 
v___x_86070__boxed_1166_ = lean_unbox(v___x_1155_);
v___x_86073__boxed_1167_ = lean_unbox(v___x_1158_);
v_res_1168_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1153_, v___x_1154_, v___x_86070__boxed_1166_, v___x_1156_, v___x_1157_, v___x_86073__boxed_1167_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v___x_1157_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v_ks_1173_; lean_object* v_vs_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1198_; 
v_ks_1173_ = lean_ctor_get(v_x_1169_, 0);
v_vs_1174_ = lean_ctor_get(v_x_1169_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1176_ = v_x_1169_;
v_isShared_1177_ = v_isSharedCheck_1198_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_vs_1174_);
lean_inc(v_ks_1173_);
lean_dec(v_x_1169_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1198_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_array_get_size(v_ks_1173_);
v___x_1179_ = lean_nat_dec_lt(v_x_1170_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_dec(v_x_1170_);
v___x_1180_ = lean_array_push(v_ks_1173_, v_x_1171_);
v___x_1181_ = lean_array_push(v_vs_1174_, v_x_1172_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1181_);
lean_ctor_set(v___x_1176_, 0, v___x_1180_);
v___x_1183_ = v___x_1176_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v_k_x27_1185_; uint8_t v___x_1186_; 
v_k_x27_1185_ = lean_array_fget_borrowed(v_ks_1173_, v_x_1170_);
v___x_1186_ = l_Lean_instBEqFVarId_beq(v_x_1171_, v_k_x27_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1188_; 
if (v_isShared_1177_ == 0)
{
v___x_1188_ = v___x_1176_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_ks_1173_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_vs_1174_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_add(v_x_1170_, v___x_1189_);
lean_dec(v_x_1170_);
v_x_1169_ = v___x_1188_;
v_x_1170_ = v___x_1190_;
goto _start;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_array_fset(v_ks_1173_, v_x_1170_, v_x_1171_);
v___x_1194_ = lean_array_fset(v_vs_1174_, v_x_1170_, v_x_1172_);
lean_dec(v_x_1170_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1194_);
lean_ctor_set(v___x_1176_, 0, v___x_1193_);
v___x_1196_ = v___x_1176_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1199_, lean_object* v_k_1200_, lean_object* v_v_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1199_, v___x_1202_, v_k_1200_, v_v_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1205_, size_t v_x_1206_, size_t v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
lean_object* v_es_1210_; size_t v___x_1211_; size_t v___x_1212_; lean_object* v_j_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_es_1210_ = lean_ctor_get(v_x_1205_, 0);
v___x_1211_ = ((size_t)31ULL);
v___x_1212_ = lean_usize_land(v_x_1206_, v___x_1211_);
v_j_1213_ = lean_usize_to_nat(v___x_1212_);
v___x_1214_ = lean_array_get_size(v_es_1210_);
v___x_1215_ = lean_nat_dec_lt(v_j_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_dec(v_j_1213_);
lean_dec(v_x_1209_);
lean_dec(v_x_1208_);
return v_x_1205_;
}
else
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1254_; 
lean_inc_ref(v_es_1210_);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_x_1205_, 0);
lean_dec(v_unused_1255_);
v___x_1217_ = v_x_1205_;
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v_x_1205_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1254_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_v_1219_; lean_object* v___x_1220_; lean_object* v_xs_x27_1221_; lean_object* v___y_1223_; 
v_v_1219_ = lean_array_fget(v_es_1210_, v_j_1213_);
v___x_1220_ = lean_box(0);
v_xs_x27_1221_ = lean_array_fset(v_es_1210_, v_j_1213_, v___x_1220_);
switch(lean_obj_tag(v_v_1219_))
{
case 0:
{
lean_object* v_key_1228_; lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1239_; 
v_key_1228_ = lean_ctor_get(v_v_1219_, 0);
v_val_1229_ = lean_ctor_get(v_v_1219_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_v_1219_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1231_ = v_v_1219_;
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_inc(v_key_1228_);
lean_dec(v_v_1219_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Lean_instBEqFVarId_beq(v_x_1208_, v_key_1228_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1231_);
v___x_1234_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1228_, v_val_1229_, v_x_1208_, v_x_1209_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
v___y_1223_ = v___x_1235_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1237_; 
lean_dec(v_val_1229_);
lean_dec(v_key_1228_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_x_1209_);
lean_ctor_set(v___x_1231_, 0, v_x_1208_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_x_1208_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_x_1209_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
}
}
}
case 1:
{
lean_object* v_node_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1252_; 
v_node_1240_ = lean_ctor_get(v_v_1219_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_v_1219_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1242_ = v_v_1219_;
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_node_1240_);
lean_dec(v_v_1219_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1244_ = ((size_t)5ULL);
v___x_1245_ = lean_usize_shift_right(v_x_1206_, v___x_1244_);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_add(v_x_1207_, v___x_1246_);
v___x_1248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1240_, v___x_1245_, v___x_1247_, v_x_1208_, v_x_1209_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1248_);
v___x_1250_ = v___x_1242_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
v___y_1223_ = v___x_1250_;
goto v___jp_1222_;
}
}
}
default: 
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_x_1208_);
lean_ctor_set(v___x_1253_, 1, v_x_1209_);
v___y_1223_ = v___x_1253_;
goto v___jp_1222_;
}
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_array_fset(v_xs_x27_1221_, v_j_1213_, v___y_1223_);
lean_dec(v_j_1213_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1224_);
v___x_1226_ = v___x_1217_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_ks_1256_; lean_object* v_vs_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1275_; 
v_ks_1256_ = lean_ctor_get(v_x_1205_, 0);
v_vs_1257_ = lean_ctor_get(v_x_1205_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1259_ = v_x_1205_;
v_isShared_1260_ = v_isSharedCheck_1275_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_vs_1257_);
lean_inc(v_ks_1256_);
lean_dec(v_x_1205_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1275_;
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
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ks_1256_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_vs_1257_);
v___x_1262_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v_newNode_1263_; size_t v___x_1264_; uint8_t v___x_1265_; 
v_newNode_1263_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1262_, v_x_1208_, v_x_1209_);
v___x_1264_ = ((size_t)7ULL);
v___x_1265_ = lean_usize_dec_le(v___x_1264_, v_x_1207_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1263_);
v___x_1267_ = lean_unsigned_to_nat(4u);
v___x_1268_ = lean_nat_dec_lt(v___x_1266_, v___x_1267_);
lean_dec(v___x_1266_);
if (v___x_1268_ == 0)
{
lean_object* v_ks_1269_; lean_object* v_vs_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_ks_1269_ = lean_ctor_get(v_newNode_1263_, 0);
lean_inc_ref(v_ks_1269_);
v_vs_1270_ = lean_ctor_get(v_newNode_1263_, 1);
lean_inc_ref(v_vs_1270_);
lean_dec_ref(v_newNode_1263_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1207_, v_ks_1269_, v_vs_1270_, v___x_1271_, v___x_1272_);
lean_dec_ref(v_vs_1270_);
lean_dec_ref(v_ks_1269_);
return v___x_1273_;
}
else
{
return v_newNode_1263_;
}
}
else
{
return v_newNode_1263_;
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
size_t v_x_86193__boxed_1308_; size_t v_x_86194__boxed_1309_; lean_object* v_res_1310_; 
v_x_86193__boxed_1308_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_x_86194__boxed_1309_ = lean_unbox_usize(v_x_1305_);
lean_dec(v_x_1305_);
v_res_1310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1303_, v_x_86193__boxed_1308_, v_x_86194__boxed_1309_, v_x_1306_, v_x_1307_);
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
uint8_t v___x_86502__boxed_1518_; uint8_t v___x_86503__boxed_1519_; uint8_t v___y_86505__boxed_1520_; lean_object* v_res_1521_; 
v___x_86502__boxed_1518_ = lean_unbox(v___x_1506_);
v___x_86503__boxed_1519_ = lean_unbox(v___x_1507_);
v___y_86505__boxed_1520_ = lean_unbox(v___y_1509_);
v_res_1521_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1504_, v_value_1505_, v___x_86502__boxed_1518_, v___x_86503__boxed_1519_, v___x_1508_, v___y_86505__boxed_1520_, v_xs_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1522_, lean_object* v_a_1523_, uint8_t v_zeta_1524_, uint8_t v___y_1525_, lean_object* v_x_1526_, uint8_t v_usedOnly_1527_, uint8_t v___x_1528_, lean_object* v_snd_1529_, lean_object* v_h_x27_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
lean_inc_ref(v_h_x27_1530_);
v___x_1539_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1522_, v_h_x27_1530_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref_known(v___x_1539_, 1);
v___x_1540_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1523_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
if (v_zeta_1524_ == 0)
{
if (v___y_1525_ == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_snd_1529_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = lean_unsigned_to_nat(2u);
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1542_);
v___x_1544_ = lean_array_push(v___x_1543_, v_x_1526_);
v___x_1545_ = lean_array_push(v___x_1544_, v_h_x27_1530_);
v___x_1546_ = 1;
v___x_1547_ = l_Lean_Meta_mkLetFVars(v___x_1545_, v_a_1541_, v_usedOnly_1527_, v___y_1525_, v___x_1546_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___x_1545_);
return v___x_1547_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v_a_1548_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1549_ = lean_unsigned_to_nat(2u);
v___x_1550_ = lean_mk_empty_array_with_capacity(v___x_1549_);
v___x_1551_ = lean_array_push(v___x_1550_, v_x_1526_);
v___x_1552_ = lean_array_push(v___x_1551_, v_h_x27_1530_);
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Meta_mkLambdaFVars(v___x_1552_, v_a_1548_, v_zeta_1524_, v___x_1528_, v_zeta_1524_, v___x_1528_, v___x_1553_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
lean_inc_ref(v_snd_1529_);
v___x_1556_ = l_Lean_Meta_mkEqRefl(v_snd_1529_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_mkAppB(v_a_1555_, v_snd_1529_, v_a_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_dec(v_a_1555_);
lean_dec_ref(v_snd_1529_);
return v___x_1556_;
}
}
else
{
lean_dec_ref(v_snd_1529_);
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1566_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_mk_empty_array_with_capacity(v___x_1567_);
lean_inc_ref(v___x_1568_);
v___x_1569_ = lean_array_push(v___x_1568_, v_x_1526_);
v___x_1570_ = lean_array_push(v___x_1569_, v_h_x27_1530_);
v___x_1571_ = l_Lean_Expr_abstractM(v_a_1566_, v___x_1570_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
lean_inc_ref(v_snd_1529_);
v___x_1573_ = l_Lean_Meta_mkEqRefl(v_snd_1529_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1584_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1578_ = lean_array_push(v___x_1568_, v_snd_1529_);
v___x_1579_ = lean_array_push(v___x_1578_, v_a_1574_);
v___x_1580_ = lean_expr_instantiate_rev(v_a_1572_, v___x_1579_);
lean_dec_ref(v___x_1579_);
lean_dec(v_a_1572_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1580_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_dec(v_a_1572_);
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_snd_1529_);
return v___x_1573_;
}
}
else
{
lean_dec_ref(v___x_1568_);
lean_dec_ref(v_snd_1529_);
return v___x_1571_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1530_);
lean_dec_ref(v_snd_1529_);
lean_dec_ref(v_x_1526_);
return v___x_1540_;
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_h_x27_1530_);
lean_dec_ref(v_snd_1529_);
lean_dec_ref(v_x_1526_);
lean_dec_ref(v_a_1523_);
v_a_1585_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1539_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1539_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1593_ = _args[0];
lean_object* v_a_1594_ = _args[1];
lean_object* v_zeta_1595_ = _args[2];
lean_object* v___y_1596_ = _args[3];
lean_object* v_x_1597_ = _args[4];
lean_object* v_usedOnly_1598_ = _args[5];
lean_object* v___x_1599_ = _args[6];
lean_object* v_snd_1600_ = _args[7];
lean_object* v_h_x27_1601_ = _args[8];
lean_object* v___y_1602_ = _args[9];
lean_object* v___y_1603_ = _args[10];
lean_object* v___y_1604_ = _args[11];
lean_object* v___y_1605_ = _args[12];
lean_object* v___y_1606_ = _args[13];
lean_object* v___y_1607_ = _args[14];
lean_object* v___y_1608_ = _args[15];
lean_object* v___y_1609_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1610_; uint8_t v___y_86729__boxed_1611_; uint8_t v_usedOnly_boxed_1612_; uint8_t v___x_86730__boxed_1613_; lean_object* v_res_1614_; 
v_zeta_boxed_1610_ = lean_unbox(v_zeta_1595_);
v___y_86729__boxed_1611_ = lean_unbox(v___y_1596_);
v_usedOnly_boxed_1612_ = lean_unbox(v_usedOnly_1598_);
v___x_86730__boxed_1613_ = lean_unbox(v___x_1599_);
v_res_1614_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1593_, v_a_1594_, v_zeta_boxed_1610_, v___y_86729__boxed_1611_, v_x_1597_, v_usedOnly_boxed_1612_, v___x_86730__boxed_1613_, v_snd_1600_, v_h_x27_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1615_, lean_object* v_a_1616_, uint8_t v_zeta_1617_, lean_object* v_x_1618_, uint8_t v_usedOnly_1619_, lean_object* v_snd_1620_, uint8_t v___y_1621_, uint8_t v___x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1615_) == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1616_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1631_) == 0)
{
if (v_zeta_1617_ == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_snd_1620_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_mk_empty_array_with_capacity(v___x_1633_);
v___x_1635_ = lean_array_push(v___x_1634_, v_x_1618_);
v___x_1636_ = 1;
v___x_1637_ = l_Lean_Meta_mkLetFVars(v___x_1635_, v_a_1632_, v_usedOnly_1619_, v_zeta_1617_, v___x_1636_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v___x_1635_);
return v___x_1637_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1638_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_mk_empty_array_with_capacity(v___x_1639_);
v___x_1641_ = lean_array_push(v___x_1640_, v_x_1618_);
v___x_1642_ = l_Lean_Expr_abstractM(v_a_1638_, v___x_1641_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v___x_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_expr_instantiate1(v_a_1643_, v_snd_1620_);
lean_dec_ref(v_snd_1620_);
lean_dec(v_a_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_dec_ref(v_snd_1620_);
return v___x_1642_;
}
}
}
else
{
lean_dec_ref(v_snd_1620_);
lean_dec_ref(v_x_1618_);
return v___x_1631_;
}
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; 
v_val_1652_ = lean_ctor_get(v_eq_x3f_1615_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v_eq_x3f_1615_, 1);
lean_inc_ref(v_snd_1620_);
lean_inc_ref(v_x_1618_);
v___x_1653_ = l_Lean_Meta_mkEq(v_x_1618_, v_snd_1620_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
lean_inc_ref(v_x_1618_);
v___x_1655_ = l_Lean_Meta_mkEqRefl(v_x_1618_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = lean_box(v_zeta_1617_);
v___x_1658_ = lean_box(v___y_1621_);
v___x_1659_ = lean_box(v_usedOnly_1619_);
v___x_1660_ = lean_box(v___x_1622_);
lean_inc(v_val_1652_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 17, 8);
lean_closure_set(v___f_1661_, 0, v_val_1652_);
lean_closure_set(v___f_1661_, 1, v_a_1616_);
lean_closure_set(v___f_1661_, 2, v___x_1657_);
lean_closure_set(v___f_1661_, 3, v___x_1658_);
lean_closure_set(v___f_1661_, 4, v_x_1618_);
lean_closure_set(v___f_1661_, 5, v___x_1659_);
lean_closure_set(v___f_1661_, 6, v___x_1660_);
lean_closure_set(v___f_1661_, 7, v_snd_1620_);
v___x_1662_ = l_Lean_TSyntax_getId(v_val_1652_);
lean_dec(v_val_1652_);
v___x_1663_ = 0;
v___x_1664_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1662_, v_a_1654_, v_a_1656_, v___f_1661_, v___x_1622_, v___x_1663_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1664_;
}
else
{
lean_dec(v_a_1654_);
lean_dec(v_val_1652_);
lean_dec_ref(v_snd_1620_);
lean_dec_ref(v_x_1618_);
lean_dec_ref(v_a_1616_);
return v___x_1655_;
}
}
else
{
lean_dec(v_val_1652_);
lean_dec_ref(v_snd_1620_);
lean_dec_ref(v_x_1618_);
lean_dec_ref(v_a_1616_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object* v_eq_x3f_1665_, lean_object* v_a_1666_, lean_object* v_zeta_1667_, lean_object* v_x_1668_, lean_object* v_usedOnly_1669_, lean_object* v_snd_1670_, lean_object* v___y_1671_, lean_object* v___x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v_zeta_boxed_1681_; uint8_t v_usedOnly_boxed_1682_; uint8_t v___y_86882__boxed_1683_; uint8_t v___x_86883__boxed_1684_; lean_object* v_res_1685_; 
v_zeta_boxed_1681_ = lean_unbox(v_zeta_1667_);
v_usedOnly_boxed_1682_ = lean_unbox(v_usedOnly_1669_);
v___y_86882__boxed_1683_ = lean_unbox(v___y_1671_);
v___x_86883__boxed_1684_ = lean_unbox(v___x_1672_);
v_res_1685_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1665_, v_a_1666_, v_zeta_boxed_1681_, v_x_1668_, v_usedOnly_boxed_1682_, v_snd_1670_, v___y_86882__boxed_1683_, v___x_86883__boxed_1684_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1686_, lean_object* v_eq_x3f_1687_, lean_object* v_a_1688_, uint8_t v_zeta_1689_, uint8_t v_usedOnly_1690_, lean_object* v_snd_1691_, uint8_t v___y_1692_, uint8_t v___x_1693_, lean_object* v_letOrReassign_1694_, lean_object* v_a_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
lean_inc_ref(v_x_1696_);
v___x_1705_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1686_, v_x_1696_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___y_1710_; lean_object* v___x_1711_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = lean_box(v_zeta_1689_);
v___x_1707_ = lean_box(v_usedOnly_1690_);
v___x_1708_ = lean_box(v___y_1692_);
v___x_1709_ = lean_box(v___x_1693_);
v___y_1710_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 16, 8);
lean_closure_set(v___y_1710_, 0, v_eq_x3f_1687_);
lean_closure_set(v___y_1710_, 1, v_a_1688_);
lean_closure_set(v___y_1710_, 2, v___x_1706_);
lean_closure_set(v___y_1710_, 3, v_x_1696_);
lean_closure_set(v___y_1710_, 4, v___x_1707_);
lean_closure_set(v___y_1710_, 5, v_snd_1691_);
lean_closure_set(v___y_1710_, 6, v___x_1708_);
lean_closure_set(v___y_1710_, 7, v___x_1709_);
v___x_1711_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1694_, v_a_1695_, v___y_1710_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_x_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_letOrReassign_1694_);
lean_dec_ref(v_snd_1691_);
lean_dec_ref(v_a_1688_);
lean_dec(v_eq_x3f_1687_);
v_a_1712_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1705_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1720_ = _args[0];
lean_object* v_eq_x3f_1721_ = _args[1];
lean_object* v_a_1722_ = _args[2];
lean_object* v_zeta_1723_ = _args[3];
lean_object* v_usedOnly_1724_ = _args[4];
lean_object* v_snd_1725_ = _args[5];
lean_object* v___y_1726_ = _args[6];
lean_object* v___x_1727_ = _args[7];
lean_object* v_letOrReassign_1728_ = _args[8];
lean_object* v_a_1729_ = _args[9];
lean_object* v_x_1730_ = _args[10];
lean_object* v___y_1731_ = _args[11];
lean_object* v___y_1732_ = _args[12];
lean_object* v___y_1733_ = _args[13];
lean_object* v___y_1734_ = _args[14];
lean_object* v___y_1735_ = _args[15];
lean_object* v___y_1736_ = _args[16];
lean_object* v___y_1737_ = _args[17];
lean_object* v___y_1738_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_1739_; uint8_t v_usedOnly_boxed_1740_; uint8_t v___y_86990__boxed_1741_; uint8_t v___x_86991__boxed_1742_; lean_object* v_res_1743_; 
v_zeta_boxed_1739_ = lean_unbox(v_zeta_1723_);
v_usedOnly_boxed_1740_ = lean_unbox(v_usedOnly_1724_);
v___y_86990__boxed_1741_ = lean_unbox(v___y_1726_);
v___x_86991__boxed_1742_ = lean_unbox(v___x_1727_);
v_res_1743_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1720_, v_eq_x3f_1721_, v_a_1722_, v_zeta_boxed_1739_, v_usedOnly_boxed_1740_, v_snd_1725_, v___y_86990__boxed_1741_, v___x_86991__boxed_1742_, v_letOrReassign_1728_, v_a_1729_, v_x_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1744_, lean_object* v_____do__lift_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1745_, v___x_1744_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1756_, lean_object* v_____do__lift_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_87058__boxed_1766_; lean_object* v_res_1767_; 
v___x_87058__boxed_1766_ = lean_unbox(v___x_1756_);
v_res_1767_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_87058__boxed_1766_, v_____do__lift_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v_____do__lift_1757_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1768_, lean_object* v___x_1769_, uint8_t v___x_1770_, lean_object* v___x_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1768_, v___x_1769_, v___x_1770_, v___x_1770_, v___x_1771_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1781_, lean_object* v___x_1782_, lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v___x_87093__boxed_1793_; lean_object* v_res_1794_; 
v___x_87093__boxed_1793_ = lean_unbox(v___x_1783_);
v_res_1794_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1781_, v___x_1782_, v___x_87093__boxed_1793_, v___x_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
lean_inc_ref(v___y_1796_);
v___x_1804_ = lean_apply_8(v_x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, lean_box(0));
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v___y_1806_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1815_, lean_object* v_mkInfoTree_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v_a_1822_, lean_object* v_a_x3f_1823_){
_start:
{
lean_object* v___x_1825_; lean_object* v_infoState_1826_; lean_object* v_trees_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_st_ref_get(v___y_1815_);
v_infoState_1826_ = lean_ctor_get(v___x_1825_, 7);
lean_inc_ref(v_infoState_1826_);
lean_dec(v___x_1825_);
v_trees_1827_ = lean_ctor_get(v_infoState_1826_, 2);
lean_inc_ref(v_trees_1827_);
lean_dec_ref(v_infoState_1826_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
v___x_1828_ = lean_apply_8(v_mkInfoTree_1816_, v_trees_1827_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1815_, lean_box(0));
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1867_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1867_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1867_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v_infoState_1834_; lean_object* v_env_1835_; lean_object* v_nextMacroScope_1836_; lean_object* v_ngen_1837_; lean_object* v_auxDeclNGen_1838_; lean_object* v_traceState_1839_; lean_object* v_cache_1840_; lean_object* v_messages_1841_; lean_object* v_snapshotTasks_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1866_; 
v___x_1833_ = lean_st_ref_take(v___y_1815_);
v_infoState_1834_ = lean_ctor_get(v___x_1833_, 7);
v_env_1835_ = lean_ctor_get(v___x_1833_, 0);
v_nextMacroScope_1836_ = lean_ctor_get(v___x_1833_, 1);
v_ngen_1837_ = lean_ctor_get(v___x_1833_, 2);
v_auxDeclNGen_1838_ = lean_ctor_get(v___x_1833_, 3);
v_traceState_1839_ = lean_ctor_get(v___x_1833_, 4);
v_cache_1840_ = lean_ctor_get(v___x_1833_, 5);
v_messages_1841_ = lean_ctor_get(v___x_1833_, 6);
v_snapshotTasks_1842_ = lean_ctor_get(v___x_1833_, 8);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1844_ = v___x_1833_;
v_isShared_1845_ = v_isSharedCheck_1866_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snapshotTasks_1842_);
lean_inc(v_infoState_1834_);
lean_inc(v_messages_1841_);
lean_inc(v_cache_1840_);
lean_inc(v_traceState_1839_);
lean_inc(v_auxDeclNGen_1838_);
lean_inc(v_ngen_1837_);
lean_inc(v_nextMacroScope_1836_);
lean_inc(v_env_1835_);
lean_dec(v___x_1833_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1866_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
uint8_t v_enabled_1846_; lean_object* v_assignment_1847_; lean_object* v_lazyAssignment_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1864_; 
v_enabled_1846_ = lean_ctor_get_uint8(v_infoState_1834_, sizeof(void*)*3);
v_assignment_1847_ = lean_ctor_get(v_infoState_1834_, 0);
v_lazyAssignment_1848_ = lean_ctor_get(v_infoState_1834_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_infoState_1834_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v_infoState_1834_, 2);
lean_dec(v_unused_1865_);
v___x_1850_ = v_infoState_1834_;
v_isShared_1851_ = v_isSharedCheck_1864_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_lazyAssignment_1848_);
lean_inc(v_assignment_1847_);
lean_dec(v_infoState_1834_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1864_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_PersistentArray_push___redArg(v_a_1822_, v_a_1829_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 2, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_assignment_1847_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_lazyAssignment_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v___x_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*3, v_enabled_1846_);
v___x_1854_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 7, v___x_1854_);
v___x_1856_ = v___x_1844_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_env_1835_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_nextMacroScope_1836_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_ngen_1837_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_auxDeclNGen_1838_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v_traceState_1839_);
lean_ctor_set(v_reuseFailAlloc_1862_, 5, v_cache_1840_);
lean_ctor_set(v_reuseFailAlloc_1862_, 6, v_messages_1841_);
lean_ctor_set(v_reuseFailAlloc_1862_, 7, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1862_, 8, v_snapshotTasks_1842_);
v___x_1856_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = lean_st_ref_put(v___y_1815_, v___x_1856_);
v___x_1858_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1858_);
v___x_1860_ = v___x_1831_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_a_1822_);
v_a_1868_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1828_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1828_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_1876_, lean_object* v_mkInfoTree_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v_a_1883_, lean_object* v_a_x3f_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1876_, v_mkInfoTree_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v_a_1883_, v_a_x3f_1884_);
lean_dec(v_a_x3f_1884_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1876_);
return v_res_1886_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_unsigned_to_nat(32u);
v___x_1888_ = lean_mk_empty_array_with_capacity(v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1890_ = ((size_t)5ULL);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_unsigned_to_nat(32u);
v___x_1893_ = lean_mk_empty_array_with_capacity(v___x_1892_);
v___x_1894_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_1895_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1893_);
lean_ctor_set(v___x_1895_, 2, v___x_1891_);
lean_ctor_set(v___x_1895_, 3, v___x_1891_);
lean_ctor_set_usize(v___x_1895_, 4, v___x_1890_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; lean_object* v_infoState_1899_; lean_object* v_trees_1900_; lean_object* v___x_1901_; lean_object* v_infoState_1902_; lean_object* v_env_1903_; lean_object* v_nextMacroScope_1904_; lean_object* v_ngen_1905_; lean_object* v_auxDeclNGen_1906_; lean_object* v_traceState_1907_; lean_object* v_cache_1908_; lean_object* v_messages_1909_; lean_object* v_snapshotTasks_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1931_; 
v___x_1898_ = lean_st_ref_get(v___y_1896_);
v_infoState_1899_ = lean_ctor_get(v___x_1898_, 7);
lean_inc_ref(v_infoState_1899_);
lean_dec(v___x_1898_);
v_trees_1900_ = lean_ctor_get(v_infoState_1899_, 2);
lean_inc_ref(v_trees_1900_);
lean_dec_ref(v_infoState_1899_);
v___x_1901_ = lean_st_ref_take(v___y_1896_);
v_infoState_1902_ = lean_ctor_get(v___x_1901_, 7);
v_env_1903_ = lean_ctor_get(v___x_1901_, 0);
v_nextMacroScope_1904_ = lean_ctor_get(v___x_1901_, 1);
v_ngen_1905_ = lean_ctor_get(v___x_1901_, 2);
v_auxDeclNGen_1906_ = lean_ctor_get(v___x_1901_, 3);
v_traceState_1907_ = lean_ctor_get(v___x_1901_, 4);
v_cache_1908_ = lean_ctor_get(v___x_1901_, 5);
v_messages_1909_ = lean_ctor_get(v___x_1901_, 6);
v_snapshotTasks_1910_ = lean_ctor_get(v___x_1901_, 8);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1912_ = v___x_1901_;
v_isShared_1913_ = v_isSharedCheck_1931_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_snapshotTasks_1910_);
lean_inc(v_infoState_1902_);
lean_inc(v_messages_1909_);
lean_inc(v_cache_1908_);
lean_inc(v_traceState_1907_);
lean_inc(v_auxDeclNGen_1906_);
lean_inc(v_ngen_1905_);
lean_inc(v_nextMacroScope_1904_);
lean_inc(v_env_1903_);
lean_dec(v___x_1901_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1931_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
uint8_t v_enabled_1914_; lean_object* v_assignment_1915_; lean_object* v_lazyAssignment_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1929_; 
v_enabled_1914_ = lean_ctor_get_uint8(v_infoState_1902_, sizeof(void*)*3);
v_assignment_1915_ = lean_ctor_get(v_infoState_1902_, 0);
v_lazyAssignment_1916_ = lean_ctor_get(v_infoState_1902_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_infoState_1902_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v_infoState_1902_, 2);
lean_dec(v_unused_1930_);
v___x_1918_ = v_infoState_1902_;
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_lazyAssignment_1916_);
lean_inc(v_assignment_1915_);
lean_dec(v_infoState_1902_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 2, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_assignment_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_lazyAssignment_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v___x_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*3, v_enabled_1914_);
v___x_1922_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 7, v___x_1922_);
v___x_1924_ = v___x_1912_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_env_1903_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_nextMacroScope_1904_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_ngen_1905_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_auxDeclNGen_1906_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_traceState_1907_);
lean_ctor_set(v_reuseFailAlloc_1927_, 5, v_cache_1908_);
lean_ctor_set(v_reuseFailAlloc_1927_, 6, v_messages_1909_);
lean_ctor_set(v_reuseFailAlloc_1927_, 7, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 8, v_snapshotTasks_1910_);
v___x_1924_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_st_ref_put(v___y_1896_, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_trees_1900_);
return v___x_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1932_);
lean_dec(v___y_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_1935_, lean_object* v_mkInfoTree_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v_infoState_1945_; uint8_t v_enabled_1946_; 
v___x_1944_ = lean_st_ref_get(v___y_1942_);
v_infoState_1945_ = lean_ctor_get(v___x_1944_, 7);
lean_inc_ref(v_infoState_1945_);
lean_dec(v___x_1944_);
v_enabled_1946_ = lean_ctor_get_uint8(v_infoState_1945_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1945_);
if (v_enabled_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref(v_mkInfoTree_1936_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
v___x_1947_ = lean_apply_7(v_x_1935_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v_r_1950_; 
v___x_1948_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1942_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
v_r_1950_ = lean_apply_7(v_x_1935_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
if (lean_obj_tag(v_r_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1975_; 
v_a_1951_ = lean_ctor_get(v_r_1950_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1953_ = v_r_1950_;
v_isShared_1954_ = v_isSharedCheck_1975_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v_r_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1975_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
lean_inc(v_a_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1942_, v_mkInfoTree_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v_a_1949_, v___x_1956_);
lean_dec_ref(v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1965_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_a_1951_);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1951_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v_a_1951_);
v_a_1966_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1957_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1957_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1976_ = lean_ctor_get(v_r_1950_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v_r_1950_, 1);
v___x_1977_ = lean_box(0);
v___x_1978_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1942_, v_mkInfoTree_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v_a_1949_, v___x_1977_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1978_, 0);
lean_dec(v_unused_1986_);
v___x_1980_ = v___x_1978_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v___x_1978_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 0, v_a_1976_);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1976_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1976_);
v_a_1987_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_1995_, lean_object* v_mkInfoTree_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_1995_, v_mkInfoTree_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2005_, lean_object* v_output_2006_, lean_object* v_trees_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_lctx_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_lctx_2015_ = lean_ctor_get(v___y_2010_, 2);
lean_inc_ref(v_lctx_2015_);
v___x_2016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2016_, 0, v_lctx_2015_);
lean_ctor_set(v___x_2016_, 1, v_stx_2005_);
lean_ctor_set(v___x_2016_, 2, v_output_2006_);
v___x_2017_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v_trees_2007_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2020_, lean_object* v_output_2021_, lean_object* v_trees_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2020_, v_output_2021_, v_trees_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2031_, lean_object* v_output_2032_, lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___f_2041_; lean_object* v___x_2042_; 
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2041_, 0, v_stx_2031_);
lean_closure_set(v___f_2041_, 1, v_output_2032_);
v___x_2042_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2033_, v___f_2041_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2043_, lean_object* v_output_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2043_, v_output_2044_, v_x_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2054_, lean_object* v_afterStx_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_inc_ref(v___y_2057_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2065_, 0, v_x_2056_);
lean_closure_set(v___f_2065_, 1, v___y_2057_);
lean_inc(v_afterStx_2055_);
lean_inc(v_beforeStx_2054_);
v___x_2066_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2066_, 0, lean_box(0));
lean_closure_set(v___x_2066_, 1, v_beforeStx_2054_);
lean_closure_set(v___x_2066_, 2, v_afterStx_2055_);
lean_closure_set(v___x_2066_, 3, v___f_2065_);
v___x_2067_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2054_, v_afterStx_2055_, v___x_2066_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2067_) == 0)
{
return v___x_2067_;
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2076_, lean_object* v_afterStx_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2076_, v_afterStx_2077_, v_x_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2087_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2091_ = l_String_toRawSubstring_x27(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2113_, uint8_t v___x_2114_, lean_object* v_config_2115_, lean_object* v_a_2116_, uint8_t v___x_2117_, lean_object* v___x_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v___f_2121_, lean_object* v___x_2122_, lean_object* v_body_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_term_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v_ref_2140_; lean_object* v___y_2141_; lean_object* v_toCold_2147_; lean_object* v_ref_2148_; lean_object* v_currMacroScope_2149_; lean_object* v_quotContext_2150_; lean_object* v_ref_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_eq_x3f_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_toCold_2147_ = lean_ctor_get(v___y_2129_, 0);
v_ref_2148_ = lean_ctor_get(v___y_2129_, 4);
v_currMacroScope_2149_ = lean_ctor_get(v___y_2129_, 9);
v_quotContext_2150_ = lean_ctor_get(v_toCold_2147_, 2);
v_ref_2151_ = l_Lean_replaceRef(v_rhs_2113_, v_ref_2148_);
v___x_2152_ = l_Lean_SourceInfo_fromRef(v_ref_2151_, v___x_2114_);
lean_dec(v_ref_2151_);
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2152_, 2);
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2156_ = lean_ctor_get(v_config_2115_, 0);
lean_inc(v_eq_x3f_2156_);
lean_dec_ref(v_config_2115_);
v___x_2157_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2149_);
lean_inc(v_quotContext_2150_);
v___x_2158_ = l_Lean_addMacroScope(v_quotContext_2150_, v___x_2157_, v_currMacroScope_2149_);
v___x_2159_ = lean_box(0);
lean_inc(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2152_);
lean_ctor_set(v___x_2160_, 1, v___x_2155_);
lean_ctor_set(v___x_2160_, 2, v___x_2158_);
lean_ctor_set(v___x_2160_, 3, v___x_2159_);
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2120_);
lean_inc_ref(v___x_2119_);
lean_inc_ref(v___x_2118_);
v___x_2162_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2161_);
v___x_2163_ = l_Lean_Syntax_node2(v___x_2152_, v___x_2162_, v___x_2154_, v___x_2160_);
if (lean_obj_tag(v_eq_x3f_2156_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2165_; 
v_val_2164_ = lean_ctor_get(v_eq_x3f_2156_, 0);
lean_inc(v_val_2164_);
lean_dec_ref_known(v_eq_x3f_2156_, 1);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc_ref(v___y_2124_);
lean_inc(v_ref_2148_);
v___x_2165_ = lean_apply_9(v___f_2121_, v_ref_2148_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_n(v_a_2166_, 23);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2120_, 5);
lean_inc_ref_n(v___x_2119_, 5);
lean_inc_ref_n(v___x_2118_, 5);
v___x_2168_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2166_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2166_);
lean_ctor_set(v___x_2171_, 1, v___x_2153_);
v___x_2172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2166_);
lean_ctor_set(v___x_2172_, 1, v___x_2155_);
lean_ctor_set(v___x_2172_, 2, v___x_2158_);
lean_ctor_set(v___x_2172_, 3, v___x_2159_);
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_a_2166_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2166_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2178_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2177_);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2166_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2182_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2166_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2185_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2166_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2188_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2166_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Lean_Syntax_node2(v_a_2166_, v___x_2184_, v_val_2164_, v___x_2190_);
v___x_2192_ = l_Lean_Syntax_node2(v_a_2166_, v___x_2188_, v___x_2191_, v___x_2163_);
v___x_2193_ = l_Lean_Syntax_node1(v_a_2166_, v___x_2184_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_a_2166_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2197_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2199_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2166_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_Syntax_node1(v_a_2166_, v___x_2184_, v___x_2122_);
v___x_2203_ = l_Lean_Syntax_node1(v_a_2166_, v___x_2184_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_a_2166_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Lean_Syntax_node4(v_a_2166_, v___x_2199_, v___x_2201_, v___x_2203_, v___x_2205_, v_body_2123_);
v___x_2207_ = l_Lean_Syntax_node1(v_a_2166_, v___x_2184_, v___x_2206_);
v___x_2208_ = l_Lean_Syntax_node1(v_a_2166_, v___x_2197_, v___x_2207_);
lean_inc_ref(v___x_2186_);
v___x_2209_ = l_Lean_Syntax_node6(v_a_2166_, v___x_2182_, v___x_2183_, v___x_2186_, v___x_2186_, v___x_2193_, v___x_2195_, v___x_2208_);
lean_inc_ref(v___x_2176_);
lean_inc_ref(v___x_2172_);
lean_inc_ref(v___x_2171_);
v___x_2210_ = l_Lean_Syntax_node5(v_a_2166_, v___x_2178_, v___x_2180_, v___x_2171_, v___x_2172_, v___x_2176_, v___x_2209_);
v___x_2211_ = l_Lean_Syntax_node7(v_a_2166_, v___x_2168_, v___x_2170_, v___x_2171_, v___x_2172_, v___x_2174_, v_rhs_2113_, v___x_2176_, v___x_2210_);
lean_inc(v_ref_2148_);
v_term_2133_ = v___x_2211_;
v___y_2134_ = v___y_2124_;
v___y_2135_ = v___y_2125_;
v___y_2136_ = v___y_2126_;
v___y_2137_ = v___y_2127_;
v___y_2138_ = v___y_2128_;
v___y_2139_ = v___y_2129_;
v_ref_2140_ = v_ref_2148_;
v___y_2141_ = v___y_2130_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_val_2164_);
lean_dec(v___x_2163_);
lean_dec(v___x_2158_);
lean_dec(v_body_2123_);
lean_dec(v___x_2122_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec_ref(v_a_2116_);
lean_dec(v_rhs_2113_);
v_a_2212_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2165_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2165_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_dec(v_eq_x3f_2156_);
lean_inc_ref(v_a_2116_);
v___x_2220_ = l_Lean_Elab_Term_exprToSyntax(v_a_2116_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc_ref(v___y_2124_);
lean_inc(v_ref_2148_);
v___x_2222_ = lean_apply_9(v___f_2121_, v_ref_2148_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, lean_box(0));
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_n(v_a_2223_, 32);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2224_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2120_, 8);
lean_inc_ref_n(v___x_2119_, 8);
lean_inc_ref_n(v___x_2118_, 8);
v___x_2225_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2224_);
v___x_2226_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_a_2223_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_a_2223_);
lean_ctor_set(v___x_2228_, 1, v___x_2153_);
v___x_2229_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2223_);
lean_ctor_set(v___x_2229_, 1, v___x_2155_);
lean_ctor_set(v___x_2229_, 2, v___x_2158_);
lean_ctor_set(v___x_2229_, 3, v___x_2159_);
v___x_2230_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2223_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_a_2223_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2235_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2234_);
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_a_2223_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2239_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2223_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
v___x_2241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2242_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2243_, 0, v_a_2223_);
lean_ctor_set(v___x_2243_, 1, v___x_2241_);
lean_ctor_set(v___x_2243_, 2, v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2245_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2244_);
v___x_2246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2223_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_a_2223_);
lean_ctor_set(v___x_2248_, 1, v___x_2244_);
v___x_2249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2250_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2249_);
v___x_2251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_a_2223_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2254_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2253_);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2256_, 0, v_a_2223_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2254_, v___x_2256_);
v___x_2258_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2257_);
v___x_2259_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_a_2223_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
lean_inc_ref_n(v___x_2243_, 2);
v___x_2261_ = l_Lean_Syntax_node5(v_a_2223_, v___x_2250_, v___x_2252_, v___x_2258_, v___x_2243_, v___x_2260_, v_a_2221_);
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2223_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
lean_inc_ref(v___x_2231_);
v___x_2264_ = l_Lean_Syntax_node5(v_a_2223_, v___x_2245_, v___x_2247_, v___x_2248_, v___x_2231_, v___x_2261_, v___x_2263_);
v___x_2265_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2264_);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2267_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2266_);
v___x_2268_ = l_Lean_Syntax_node2(v_a_2223_, v___x_2267_, v___x_2243_, v___x_2163_);
v___x_2269_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_a_2223_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2273_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2275_ = l_Lean_Name_mkStr4(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_a_2223_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2122_);
v___x_2279_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2223_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_node4(v_a_2223_, v___x_2275_, v___x_2277_, v___x_2279_, v___x_2281_, v_body_2123_);
v___x_2283_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2241_, v___x_2282_);
v___x_2284_ = l_Lean_Syntax_node1(v_a_2223_, v___x_2273_, v___x_2283_);
v___x_2285_ = l_Lean_Syntax_node6(v_a_2223_, v___x_2239_, v___x_2240_, v___x_2243_, v___x_2265_, v___x_2269_, v___x_2271_, v___x_2284_);
lean_inc_ref(v___x_2233_);
lean_inc_ref(v___x_2229_);
lean_inc_ref(v___x_2228_);
v___x_2286_ = l_Lean_Syntax_node5(v_a_2223_, v___x_2235_, v___x_2237_, v___x_2228_, v___x_2229_, v___x_2233_, v___x_2285_);
v___x_2287_ = l_Lean_Syntax_node7(v_a_2223_, v___x_2225_, v___x_2227_, v___x_2228_, v___x_2229_, v___x_2231_, v_rhs_2113_, v___x_2233_, v___x_2286_);
lean_inc(v_ref_2148_);
v_term_2133_ = v___x_2287_;
v___y_2134_ = v___y_2124_;
v___y_2135_ = v___y_2125_;
v___y_2136_ = v___y_2126_;
v___y_2137_ = v___y_2127_;
v___y_2138_ = v___y_2128_;
v___y_2139_ = v___y_2129_;
v_ref_2140_ = v_ref_2148_;
v___y_2141_ = v___y_2130_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2221_);
lean_dec(v___x_2163_);
lean_dec(v___x_2158_);
lean_dec(v_body_2123_);
lean_dec(v___x_2122_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec_ref(v_a_2116_);
lean_dec(v_rhs_2113_);
v_a_2288_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2222_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2222_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v___x_2163_);
lean_dec(v___x_2158_);
lean_dec(v_body_2123_);
lean_dec(v___x_2122_);
lean_dec_ref(v___f_2121_);
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec_ref(v___x_2118_);
lean_dec_ref(v_a_2116_);
lean_dec(v_rhs_2113_);
v_a_2296_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2220_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2220_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
v___jp_2132_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; 
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_a_2116_);
v___x_2143_ = lean_box(0);
v___x_2144_ = lean_box(v___x_2117_);
lean_inc(v_term_2133_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2145_, 0, v_term_2133_);
lean_closure_set(v___f_2145_, 1, v___x_2142_);
lean_closure_set(v___f_2145_, 2, v___x_2144_);
lean_closure_set(v___f_2145_, 3, v___x_2143_);
v___x_2146_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2140_, v_term_2133_, v___f_2145_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2141_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2304_ = _args[0];
lean_object* v___x_2305_ = _args[1];
lean_object* v_config_2306_ = _args[2];
lean_object* v_a_2307_ = _args[3];
lean_object* v___x_2308_ = _args[4];
lean_object* v___x_2309_ = _args[5];
lean_object* v___x_2310_ = _args[6];
lean_object* v___x_2311_ = _args[7];
lean_object* v___f_2312_ = _args[8];
lean_object* v___x_2313_ = _args[9];
lean_object* v_body_2314_ = _args[10];
lean_object* v___y_2315_ = _args[11];
lean_object* v___y_2316_ = _args[12];
lean_object* v___y_2317_ = _args[13];
lean_object* v___y_2318_ = _args[14];
lean_object* v___y_2319_ = _args[15];
lean_object* v___y_2320_ = _args[16];
lean_object* v___y_2321_ = _args[17];
lean_object* v___y_2322_ = _args[18];
_start:
{
uint8_t v___x_87622__boxed_2323_; uint8_t v___x_87624__boxed_2324_; lean_object* v_res_2325_; 
v___x_87622__boxed_2323_ = lean_unbox(v___x_2305_);
v___x_87624__boxed_2324_ = lean_unbox(v___x_2308_);
v_res_2325_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2304_, v___x_87622__boxed_2323_, v_config_2306_, v_a_2307_, v___x_87624__boxed_2324_, v___x_2309_, v___x_2310_, v___x_2311_, v___f_2312_, v___x_2313_, v_body_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2326_, lean_object* v___y_2327_){
_start:
{
if (lean_obj_tag(v_x_2326_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v_x_2326_, 0);
lean_inc(v_a_2328_);
v___x_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2328_);
lean_ctor_set(v___x_2329_, 1, v___y_2327_);
return v___x_2329_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v_x_2326_, 0);
lean_inc(v_a_2330_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2330_);
lean_ctor_set(v___x_2331_, 1, v___y_2327_);
return v___x_2331_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2332_, v___y_2333_);
lean_dec_ref(v_x_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2335_, lean_object* v_stx_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2335_, v_stx_2336_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
if (lean_obj_tag(v_a_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
v_a_2341_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2350_);
v___x_2343_ = v___x_2339_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_a_2341_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_val_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2379_; 
v_val_2351_ = lean_ctor_get(v_a_2340_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_a_2340_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2353_ = v_a_2340_;
v_isShared_2354_ = v_isSharedCheck_2379_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_val_2351_);
lean_dec(v_a_2340_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2379_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_snd_2355_; 
v_snd_2355_ = lean_ctor_get(v_val_2351_, 1);
lean_inc(v_snd_2355_);
lean_dec(v_val_2351_);
if (lean_obj_tag(v_snd_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2353_);
v_a_2356_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2339_, 2);
v_a_2357_ = lean_ctor_get(v_snd_2355_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_snd_2355_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2359_ = v_snd_2355_;
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v_snd_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2362_, v_a_2356_);
lean_dec_ref(v___x_2362_);
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2378_; 
v_a_2366_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2339_, 2);
v_a_2367_ = lean_ctor_get(v_snd_2355_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_snd_2355_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2369_ = v_snd_2355_;
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v_snd_2355_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v_a_2367_);
v___x_2372_ = v___x_2353_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2374_, v_a_2366_);
lean_dec_ref(v___x_2374_);
return v___x_2375_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2380_ = lean_ctor_get(v___x_2339_, 0);
v_a_2381_ = lean_ctor_get(v___x_2339_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2339_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_inc(v_a_2380_);
lean_dec(v___x_2339_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2380_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2389_, lean_object* v_stx_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2389_, v_stx_2390_, v___y_2391_, v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_currNamespace_2394_);
lean_ctor_set(v___x_2397_, 1, v___y_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2398_, v___y_2399_, v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2402_, lean_object* v_currNamespace_2403_, lean_object* v_openDecls_2404_, lean_object* v_n_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = l_Lean_ResolveName_resolveNamespace(v_env_2402_, v_currNamespace_2403_, v_openDecls_2404_, v_n_2405_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___y_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2410_, lean_object* v_currNamespace_2411_, lean_object* v_openDecls_2412_, lean_object* v_n_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2410_, v_currNamespace_2411_, v_openDecls_2412_, v_n_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2417_, lean_object* v_declName_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v___x_2421_; lean_object* v_env_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2421_ = 0;
v_env_2422_ = l_Lean_Environment_setExporting(v_env_2417_, v___x_2421_);
lean_inc(v_declName_2418_);
v___x_2423_ = l_Lean_mkPrivateName(v_env_2422_, v_declName_2418_);
v___x_2424_ = 1;
lean_inc_ref(v_env_2422_);
v___x_2425_ = l_Lean_Environment_contains(v_env_2422_, v___x_2423_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = l_Lean_privateToUserName(v_declName_2418_);
v___x_2427_ = l_Lean_Environment_contains(v_env_2422_, v___x_2426_, v___x_2424_);
v___x_2428_ = lean_box(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___y_2420_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v_env_2422_);
lean_dec(v_declName_2418_);
v___x_2430_ = lean_box(v___x_2425_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___y_2420_);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2432_, lean_object* v_declName_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2432_, v_declName_2433_, v___y_2434_, v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2436_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2437_; double v___x_2438_; 
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_float_of_nat(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2441_, lean_object* v_msg_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_ref_2448_; lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2494_; 
v_ref_2448_ = lean_ctor_get(v___y_2445_, 4);
v___x_2449_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2494_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2494_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v_traceState_2455_; lean_object* v_env_2456_; lean_object* v_nextMacroScope_2457_; lean_object* v_ngen_2458_; lean_object* v_auxDeclNGen_2459_; lean_object* v_cache_2460_; lean_object* v_messages_2461_; lean_object* v_infoState_2462_; lean_object* v_snapshotTasks_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2493_; 
v___x_2454_ = lean_st_ref_take(v___y_2446_);
v_traceState_2455_ = lean_ctor_get(v___x_2454_, 4);
v_env_2456_ = lean_ctor_get(v___x_2454_, 0);
v_nextMacroScope_2457_ = lean_ctor_get(v___x_2454_, 1);
v_ngen_2458_ = lean_ctor_get(v___x_2454_, 2);
v_auxDeclNGen_2459_ = lean_ctor_get(v___x_2454_, 3);
v_cache_2460_ = lean_ctor_get(v___x_2454_, 5);
v_messages_2461_ = lean_ctor_get(v___x_2454_, 6);
v_infoState_2462_ = lean_ctor_get(v___x_2454_, 7);
v_snapshotTasks_2463_ = lean_ctor_get(v___x_2454_, 8);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2465_ = v___x_2454_;
v_isShared_2466_ = v_isSharedCheck_2493_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_snapshotTasks_2463_);
lean_inc(v_infoState_2462_);
lean_inc(v_messages_2461_);
lean_inc(v_cache_2460_);
lean_inc(v_traceState_2455_);
lean_inc(v_auxDeclNGen_2459_);
lean_inc(v_ngen_2458_);
lean_inc(v_nextMacroScope_2457_);
lean_inc(v_env_2456_);
lean_dec(v___x_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2493_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
uint64_t v_tid_2467_; lean_object* v_traces_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2492_; 
v_tid_2467_ = lean_ctor_get_uint64(v_traceState_2455_, sizeof(void*)*1);
v_traces_2468_ = lean_ctor_get(v_traceState_2455_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_traceState_2455_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2470_ = v_traceState_2455_;
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_traces_2468_);
lean_dec(v_traceState_2455_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2492_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; double v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2474_ = 0;
v___x_2475_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2476_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2476_, 0, v_cls_2441_);
lean_ctor_set(v___x_2476_, 1, v___x_2472_);
lean_ctor_set(v___x_2476_, 2, v___x_2475_);
lean_ctor_set_float(v___x_2476_, sizeof(void*)*3, v___x_2473_);
lean_ctor_set_float(v___x_2476_, sizeof(void*)*3 + 8, v___x_2473_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*3 + 16, v___x_2474_);
v___x_2477_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2478_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v_a_2450_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
lean_inc(v_ref_2448_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v_ref_2448_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_PersistentArray_push___redArg(v_traces_2468_, v___x_2479_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2480_);
v___x_2482_ = v___x_2470_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2480_);
lean_ctor_set_uint64(v_reuseFailAlloc_2491_, sizeof(void*)*1, v_tid_2467_);
v___x_2482_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2484_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 4, v___x_2482_);
v___x_2484_ = v___x_2465_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_env_2456_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_nextMacroScope_2457_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_ngen_2458_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_auxDeclNGen_2459_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2490_, 5, v_cache_2460_);
lean_ctor_set(v_reuseFailAlloc_2490_, 6, v_messages_2461_);
lean_ctor_set(v_reuseFailAlloc_2490_, 7, v_infoState_2462_);
lean_ctor_set(v_reuseFailAlloc_2490_, 8, v_snapshotTasks_2463_);
v___x_2484_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2485_ = lean_st_ref_put(v___y_2446_, v___x_2484_);
v___x_2486_ = lean_box(0);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2486_);
v___x_2488_ = v___x_2452_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2495_, lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2495_, v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
if (lean_obj_tag(v_as_2506_) == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
else
{
lean_object* v_options_2517_; uint8_t v_hasTrace_2518_; 
v_options_2517_ = lean_ctor_get(v___y_2512_, 1);
v_hasTrace_2518_ = lean_ctor_get_uint8(v_options_2517_, sizeof(void*)*1);
if (v_hasTrace_2518_ == 0)
{
lean_object* v_tail_2519_; 
v_tail_2519_ = lean_ctor_get(v_as_2506_, 1);
lean_inc(v_tail_2519_);
lean_dec_ref_known(v_as_2506_, 2);
v_as_2506_ = v_tail_2519_;
goto _start;
}
else
{
lean_object* v_head_2521_; lean_object* v_toCold_2522_; lean_object* v_tail_2523_; lean_object* v_fst_2524_; lean_object* v_snd_2525_; lean_object* v_inheritedTraceOptions_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_head_2521_ = lean_ctor_get(v_as_2506_, 0);
v_toCold_2522_ = lean_ctor_get(v___y_2512_, 0);
lean_inc(v_head_2521_);
v_tail_2523_ = lean_ctor_get(v_as_2506_, 1);
lean_inc(v_tail_2523_);
lean_dec_ref_known(v_as_2506_, 2);
v_fst_2524_ = lean_ctor_get(v_head_2521_, 0);
lean_inc_n(v_fst_2524_, 2);
v_snd_2525_ = lean_ctor_get(v_head_2521_, 1);
lean_inc(v_snd_2525_);
lean_dec(v_head_2521_);
v_inheritedTraceOptions_2526_ = lean_ctor_get(v_toCold_2522_, 4);
v___x_2527_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2528_ = l_Lean_Name_append(v___x_2527_, v_fst_2524_);
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2526_, v_options_2517_, v___x_2528_);
lean_dec(v___x_2528_);
if (v___x_2529_ == 0)
{
lean_dec(v_snd_2525_);
lean_dec(v_fst_2524_);
v_as_2506_ = v_tail_2523_;
goto _start;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_snd_2525_);
v___x_2532_ = l_Lean_MessageData_ofFormat(v___x_2531_);
v___x_2533_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2524_, v___x_2532_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
v_as_2506_ = v_tail_2523_;
goto _start;
}
else
{
lean_dec(v_tail_2523_);
return v___x_2533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2544_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2545_, lean_object* v_i_2546_, lean_object* v_k_2547_){
_start:
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = lean_array_get_size(v_keys_2545_);
v___x_2549_ = lean_nat_dec_lt(v_i_2546_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec(v_i_2546_);
return v___x_2549_;
}
else
{
lean_object* v_k_x27_2550_; uint8_t v___x_2551_; 
v_k_x27_2550_ = lean_array_fget_borrowed(v_keys_2545_, v_i_2546_);
v___x_2551_ = l_Lean_instBEqExtraModUse_beq(v_k_2547_, v_k_x27_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(1u);
v___x_2553_ = lean_nat_add(v_i_2546_, v___x_2552_);
lean_dec(v_i_2546_);
v_i_2546_ = v___x_2553_;
goto _start;
}
else
{
lean_dec(v_i_2546_);
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2555_, lean_object* v_i_2556_, lean_object* v_k_2557_){
_start:
{
uint8_t v_res_2558_; lean_object* v_r_2559_; 
v_res_2558_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2555_, v_i_2556_, v_k_2557_);
lean_dec_ref(v_k_2557_);
lean_dec_ref(v_keys_2555_);
v_r_2559_ = lean_box(v_res_2558_);
return v_r_2559_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2560_, size_t v_x_2561_, lean_object* v_x_2562_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v_es_2563_; lean_object* v___x_2564_; size_t v___x_2565_; size_t v___x_2566_; lean_object* v_j_2567_; lean_object* v___x_2568_; 
v_es_2563_ = lean_ctor_get(v_x_2560_, 0);
v___x_2564_ = lean_box(2);
v___x_2565_ = ((size_t)31ULL);
v___x_2566_ = lean_usize_land(v_x_2561_, v___x_2565_);
v_j_2567_ = lean_usize_to_nat(v___x_2566_);
v___x_2568_ = lean_array_get_borrowed(v___x_2564_, v_es_2563_, v_j_2567_);
lean_dec(v_j_2567_);
switch(lean_obj_tag(v___x_2568_))
{
case 0:
{
lean_object* v_key_2569_; uint8_t v___x_2570_; 
v_key_2569_ = lean_ctor_get(v___x_2568_, 0);
v___x_2570_ = l_Lean_instBEqExtraModUse_beq(v_x_2562_, v_key_2569_);
return v___x_2570_;
}
case 1:
{
lean_object* v_node_2571_; size_t v___x_2572_; size_t v___x_2573_; 
v_node_2571_ = lean_ctor_get(v___x_2568_, 0);
v___x_2572_ = ((size_t)5ULL);
v___x_2573_ = lean_usize_shift_right(v_x_2561_, v___x_2572_);
v_x_2560_ = v_node_2571_;
v_x_2561_ = v___x_2573_;
goto _start;
}
default: 
{
uint8_t v___x_2575_; 
v___x_2575_ = 0;
return v___x_2575_;
}
}
}
else
{
lean_object* v_ks_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_ks_2576_ = lean_ctor_get(v_x_2560_, 0);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2576_, v___x_2577_, v_x_2562_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_){
_start:
{
size_t v_x_88366__boxed_2582_; uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_x_88366__boxed_2582_ = lean_unbox_usize(v_x_2580_);
lean_dec(v_x_2580_);
v_res_2583_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2579_, v_x_88366__boxed_2582_, v_x_2581_);
lean_dec_ref(v_x_2581_);
lean_dec_ref(v_x_2579_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
uint64_t v___x_2587_; size_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = l_Lean_instHashableExtraModUse_hash(v_x_2586_);
v___x_2588_ = lean_uint64_to_usize(v___x_2587_);
v___x_2589_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2585_, v___x_2588_, v_x_2586_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2590_, v_x_2591_);
lean_dec_ref(v_x_2591_);
lean_dec_ref(v_x_2590_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2597_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2598_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2599_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2605_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
lean_ctor_set(v___x_2605_, 2, v___x_2604_);
lean_ctor_set(v___x_2605_, 3, v___x_2604_);
lean_ctor_set(v___x_2605_, 4, v___x_2604_);
lean_ctor_set(v___x_2605_, 5, v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_cls_2617_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2618_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2619_ = l_Lean_Name_append(v___x_2618_, v_cls_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2630_, uint8_t v_isMeta_2631_, lean_object* v_hint_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v_env_2642_; uint8_t v_isExporting_2643_; lean_object* v___x_2644_; lean_object* v_env_2645_; lean_object* v___x_2646_; lean_object* v_entry_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2641_ = lean_st_ref_get(v___y_2639_);
v_env_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc_ref(v_env_2642_);
lean_dec(v___x_2641_);
v_isExporting_2643_ = lean_ctor_get_uint8(v_env_2642_, sizeof(void*)*8);
lean_dec_ref(v_env_2642_);
v___x_2644_ = lean_st_ref_get(v___y_2639_);
v_env_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc_ref(v_env_2645_);
lean_dec(v___x_2644_);
v___x_2646_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2630_);
v_entry_2647_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2647_, 0, v_mod_2630_);
lean_ctor_set_uint8(v_entry_2647_, sizeof(void*)*1, v_isExporting_2643_);
lean_ctor_set_uint8(v_entry_2647_, sizeof(void*)*1 + 1, v_isMeta_2631_);
v___x_2648_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2649_ = lean_box(1);
v___x_2650_ = lean_box(0);
v___x_2693_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2646_, v___x_2648_, v_env_2645_, v___x_2649_, v___x_2650_);
v___x_2694_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2693_, v_entry_2647_);
lean_dec(v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v_options_2695_; uint8_t v_hasTrace_2696_; 
v_options_2695_ = lean_ctor_get(v___y_2638_, 1);
v_hasTrace_2696_ = lean_ctor_get_uint8(v_options_2695_, sizeof(void*)*1);
if (v_hasTrace_2696_ == 0)
{
lean_dec(v_hint_2632_);
lean_dec(v_mod_2630_);
v___y_2652_ = v___y_2637_;
v___y_2653_ = v___y_2639_;
goto v___jp_2651_;
}
else
{
lean_object* v_toCold_2697_; lean_object* v_inheritedTraceOptions_2698_; lean_object* v_cls_2699_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_toCold_2697_ = lean_ctor_get(v___y_2638_, 0);
v_inheritedTraceOptions_2698_ = lean_ctor_get(v_toCold_2697_, 4);
v_cls_2699_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2719_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2698_, v_options_2695_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_dec(v_hint_2632_);
lean_dec(v_mod_2630_);
v___y_2652_ = v___y_2637_;
v___y_2653_ = v___y_2639_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2721_; lean_object* v___y_2723_; 
v___x_2721_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2643_ == 0)
{
lean_object* v___x_2730_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2723_ = v___x_2730_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2731_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2723_ = v___x_2731_;
goto v___jp_2722_;
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_inc_ref(v___y_2723_);
v___x_2724_ = l_Lean_stringToMessageData(v___y_2723_);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2721_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2725_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
if (v_isMeta_2631_ == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2706_ = v___x_2727_;
v___y_2707_ = v___x_2728_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2729_; 
v___x_2729_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2706_ = v___x_2727_;
v___y_2707_ = v___x_2729_;
goto v___jp_2705_;
}
}
}
v___jp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2701_);
lean_ctor_set(v___x_2703_, 1, v___y_2702_);
v___x_2704_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2699_, v___x_2703_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_dec_ref_known(v___x_2704_, 1);
v___y_2652_ = v___y_2637_;
v___y_2653_ = v___y_2639_;
goto v___jp_2651_;
}
else
{
lean_dec_ref_known(v_entry_2647_, 1);
return v___x_2704_;
}
}
v___jp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
lean_inc_ref(v___y_2707_);
v___x_2708_ = l_Lean_stringToMessageData(v___y_2707_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = l_Lean_MessageData_ofName(v_mod_2630_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_Name_isAnonymous(v_hint_2632_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2716_ = l_Lean_MessageData_ofName(v_hint_2632_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___y_2701_ = v___x_2713_;
v___y_2702_ = v___x_2717_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2718_; 
lean_dec(v_hint_2632_);
v___x_2718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2701_ = v___x_2713_;
v___y_2702_ = v___x_2718_;
goto v___jp_2700_;
}
}
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref_known(v_entry_2647_, 1);
lean_dec(v_hint_2632_);
lean_dec(v_mod_2630_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
v___jp_2651_:
{
lean_object* v___x_2654_; lean_object* v_toEnvExtension_2655_; lean_object* v_env_2656_; lean_object* v_nextMacroScope_2657_; lean_object* v_ngen_2658_; lean_object* v_auxDeclNGen_2659_; lean_object* v_traceState_2660_; lean_object* v_messages_2661_; lean_object* v_infoState_2662_; lean_object* v_snapshotTasks_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2691_; 
v___x_2654_ = lean_st_ref_take(v___y_2653_);
v_toEnvExtension_2655_ = lean_ctor_get(v___x_2648_, 0);
v_env_2656_ = lean_ctor_get(v___x_2654_, 0);
v_nextMacroScope_2657_ = lean_ctor_get(v___x_2654_, 1);
v_ngen_2658_ = lean_ctor_get(v___x_2654_, 2);
v_auxDeclNGen_2659_ = lean_ctor_get(v___x_2654_, 3);
v_traceState_2660_ = lean_ctor_get(v___x_2654_, 4);
v_messages_2661_ = lean_ctor_get(v___x_2654_, 6);
v_infoState_2662_ = lean_ctor_get(v___x_2654_, 7);
v_snapshotTasks_2663_ = lean_ctor_get(v___x_2654_, 8);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; 
v_unused_2692_ = lean_ctor_get(v___x_2654_, 5);
lean_dec(v_unused_2692_);
v___x_2665_ = v___x_2654_;
v_isShared_2666_ = v_isSharedCheck_2691_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snapshotTasks_2663_);
lean_inc(v_infoState_2662_);
lean_inc(v_messages_2661_);
lean_inc(v_traceState_2660_);
lean_inc(v_auxDeclNGen_2659_);
lean_inc(v_ngen_2658_);
lean_inc(v_nextMacroScope_2657_);
lean_inc(v_env_2656_);
lean_dec(v___x_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2691_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_asyncMode_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v_asyncMode_2667_ = lean_ctor_get(v_toEnvExtension_2655_, 2);
v___x_2668_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2648_, v_env_2656_, v_entry_2647_, v_asyncMode_2667_, v___x_2650_);
v___x_2669_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 5, v___x_2669_);
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2671_ = v___x_2665_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_nextMacroScope_2657_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_ngen_2658_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_auxDeclNGen_2659_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_traceState_2660_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_messages_2661_);
lean_ctor_set(v_reuseFailAlloc_2690_, 7, v_infoState_2662_);
lean_ctor_set(v_reuseFailAlloc_2690_, 8, v_snapshotTasks_2663_);
v___x_2671_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v_mctx_2674_; lean_object* v_zetaDeltaFVarIds_2675_; lean_object* v_postponed_2676_; lean_object* v_diag_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2688_; 
v___x_2672_ = lean_st_ref_put(v___y_2653_, v___x_2671_);
v___x_2673_ = lean_st_ref_take(v___y_2652_);
v_mctx_2674_ = lean_ctor_get(v___x_2673_, 0);
v_zetaDeltaFVarIds_2675_ = lean_ctor_get(v___x_2673_, 2);
v_postponed_2676_ = lean_ctor_get(v___x_2673_, 3);
v_diag_2677_ = lean_ctor_get(v___x_2673_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2673_, 1);
lean_dec(v_unused_2689_);
v___x_2679_ = v___x_2673_;
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_diag_2677_);
lean_inc(v_postponed_2676_);
lean_inc(v_zetaDeltaFVarIds_2675_);
lean_inc(v_mctx_2674_);
lean_dec(v___x_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 1, v___x_2681_);
v___x_2683_ = v___x_2679_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_mctx_2674_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_zetaDeltaFVarIds_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_postponed_2676_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_diag_2677_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_st_ref_put(v___y_2652_, v___x_2683_);
v___x_2685_ = lean_box(0);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2734_, lean_object* v_isMeta_2735_, lean_object* v_hint_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
uint8_t v_isMeta_boxed_2745_; lean_object* v_res_2746_; 
v_isMeta_boxed_2745_ = lean_unbox(v_isMeta_2735_);
v_res_2746_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2734_, v_isMeta_boxed_2745_, v_hint_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2747_, lean_object* v_declName_2748_, lean_object* v_as_2749_, size_t v_sz_2750_, size_t v_i_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_usize_dec_lt(v_i_2751_, v_sz_2750_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_dec(v_declName_2748_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_b_2752_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; lean_object* v_modules_2764_; lean_object* v___x_2765_; lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v_toImport_2768_; lean_object* v_module_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; 
v___x_2763_ = l_Lean_Environment_header(v___x_2747_);
v_modules_2764_ = lean_ctor_get(v___x_2763_, 3);
lean_inc_ref(v_modules_2764_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2766_ = lean_array_uget_borrowed(v_as_2749_, v_i_2751_);
v___x_2767_ = lean_array_get(v___x_2765_, v_modules_2764_, v_a_2766_);
lean_dec_ref(v_modules_2764_);
v_toImport_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc_ref(v_toImport_2768_);
lean_dec(v___x_2767_);
v_module_2769_ = lean_ctor_get(v_toImport_2768_, 0);
lean_inc(v_module_2769_);
lean_dec_ref(v_toImport_2768_);
v___x_2770_ = 0;
lean_inc(v_declName_2748_);
v___x_2771_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2769_, v___x_2770_, v_declName_2748_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; size_t v___x_2773_; size_t v___x_2774_; 
lean_dec_ref_known(v___x_2771_, 1);
v___x_2772_ = lean_box(0);
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2751_, v___x_2773_);
v_i_2751_ = v___x_2774_;
v_b_2752_ = v___x_2772_;
goto _start;
}
else
{
lean_dec(v_declName_2748_);
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2776_, lean_object* v_declName_2777_, lean_object* v_as_2778_, lean_object* v_sz_2779_, lean_object* v_i_2780_, lean_object* v_b_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
size_t v_sz_boxed_2790_; size_t v_i_boxed_2791_; lean_object* v_res_2792_; 
v_sz_boxed_2790_ = lean_unbox_usize(v_sz_2779_);
lean_dec(v_sz_2779_);
v_i_boxed_2791_ = lean_unbox_usize(v_i_2780_);
lean_dec(v_i_2780_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2776_, v_declName_2777_, v_as_2778_, v_sz_boxed_2790_, v_i_boxed_2791_, v_b_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_as_2778_);
lean_dec_ref(v___x_2776_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_a_2793_, lean_object* v_x_2794_){
_start:
{
if (lean_obj_tag(v_x_2794_) == 0)
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_box(0);
return v___x_2795_;
}
else
{
lean_object* v_key_2796_; lean_object* v_value_2797_; lean_object* v_tail_2798_; uint8_t v___x_2799_; 
v_key_2796_ = lean_ctor_get(v_x_2794_, 0);
v_value_2797_ = lean_ctor_get(v_x_2794_, 1);
v_tail_2798_ = lean_ctor_get(v_x_2794_, 2);
v___x_2799_ = lean_name_eq(v_key_2796_, v_a_2793_);
if (v___x_2799_ == 0)
{
v_x_2794_ = v_tail_2798_;
goto _start;
}
else
{
lean_object* v___x_2801_; 
lean_inc(v_value_2797_);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_value_2797_);
return v___x_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_2802_, lean_object* v_x_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2802_, v_x_2803_);
lean_dec(v_x_2803_);
lean_dec(v_a_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_buckets_2807_; lean_object* v___x_2808_; uint64_t v___y_2810_; 
v_buckets_2807_ = lean_ctor_get(v_m_2805_, 1);
v___x_2808_ = lean_array_get_size(v_buckets_2807_);
if (lean_obj_tag(v_a_2806_) == 0)
{
uint64_t v___x_2824_; 
v___x_2824_ = 1723ULL;
v___y_2810_ = v___x_2824_;
goto v___jp_2809_;
}
else
{
uint64_t v_hash_2825_; 
v_hash_2825_ = lean_ctor_get_uint64(v_a_2806_, sizeof(void*)*2);
v___y_2810_ = v_hash_2825_;
goto v___jp_2809_;
}
v___jp_2809_:
{
uint64_t v___x_2811_; uint64_t v___x_2812_; uint64_t v_fold_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint64_t v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2811_ = 32ULL;
v___x_2812_ = lean_uint64_shift_right(v___y_2810_, v___x_2811_);
v_fold_2813_ = lean_uint64_xor(v___y_2810_, v___x_2812_);
v___x_2814_ = 16ULL;
v___x_2815_ = lean_uint64_shift_right(v_fold_2813_, v___x_2814_);
v___x_2816_ = lean_uint64_xor(v_fold_2813_, v___x_2815_);
v___x_2817_ = lean_uint64_to_usize(v___x_2816_);
v___x_2818_ = lean_usize_of_nat(v___x_2808_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_sub(v___x_2818_, v___x_2819_);
v___x_2821_ = lean_usize_land(v___x_2817_, v___x_2820_);
v___x_2822_ = lean_array_uget_borrowed(v_buckets_2807_, v___x_2821_);
v___x_2823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2806_, v___x_2822_);
return v___x_2823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_m_2826_);
return v_res_2828_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2832_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2833_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2832_, v___x_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2836_, uint8_t v_isMeta_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v_env_2850_; lean_object* v___y_2852_; lean_object* v___x_2865_; 
v___x_2846_ = lean_st_ref_get(v___y_2844_);
v_env_2850_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2850_);
lean_dec(v___x_2846_);
v___x_2865_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2850_, v_declName_2836_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec_ref(v_env_2850_);
lean_dec(v_declName_2836_);
goto v___jp_2847_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2867_; lean_object* v_modules_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v_val_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = l_Lean_Environment_header(v_env_2850_);
v_modules_2868_ = lean_ctor_get(v___x_2867_, 3);
lean_inc_ref(v_modules_2868_);
lean_dec_ref(v___x_2867_);
v___x_2869_ = lean_array_get_size(v_modules_2868_);
v___x_2870_ = lean_nat_dec_lt(v_val_2866_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_dec_ref(v_modules_2868_);
lean_dec(v_val_2866_);
lean_dec_ref(v_env_2850_);
lean_dec(v_declName_2836_);
goto v___jp_2847_;
}
else
{
lean_object* v___x_2871_; lean_object* v_env_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___y_2876_; 
v___x_2871_ = lean_st_ref_get(v___y_2844_);
v_env_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc_ref(v_env_2872_);
lean_dec(v___x_2871_);
v___x_2873_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2874_ = lean_array_fget(v_modules_2868_, v_val_2866_);
lean_dec(v_val_2866_);
lean_dec_ref(v_modules_2868_);
if (v_isMeta_2837_ == 0)
{
lean_dec_ref(v_env_2872_);
v___y_2876_ = v_isMeta_2837_;
goto v___jp_2875_;
}
else
{
uint8_t v___x_2887_; 
lean_inc(v_declName_2836_);
v___x_2887_ = l_Lean_isMarkedMeta(v_env_2872_, v_declName_2836_);
if (v___x_2887_ == 0)
{
v___y_2876_ = v_isMeta_2837_;
goto v___jp_2875_;
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = 0;
v___y_2876_ = v___x_2888_;
goto v___jp_2875_;
}
}
v___jp_2875_:
{
lean_object* v_toImport_2877_; lean_object* v_module_2878_; lean_object* v___x_2879_; 
v_toImport_2877_ = lean_ctor_get(v___x_2874_, 0);
lean_inc_ref(v_toImport_2877_);
lean_dec(v___x_2874_);
v_module_2878_ = lean_ctor_get(v_toImport_2877_, 0);
lean_inc(v_module_2878_);
lean_dec_ref(v_toImport_2877_);
lean_inc(v_declName_2836_);
v___x_2879_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2878_, v___y_2876_, v_declName_2836_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref_known(v___x_2879_, 1);
v___x_2880_ = l_Lean_indirectModUseExt;
v___x_2881_ = lean_box(1);
v___x_2882_ = lean_box(0);
lean_inc_ref(v_env_2850_);
v___x_2883_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2873_, v___x_2880_, v_env_2850_, v___x_2881_, v___x_2882_);
v___x_2884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_2883_, v_declName_2836_);
lean_dec(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2852_ = v___x_2885_;
goto v___jp_2851_;
}
else
{
lean_object* v_val_2886_; 
v_val_2886_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v___x_2884_, 1);
v___y_2852_ = v_val_2886_;
goto v___jp_2851_;
}
}
else
{
lean_dec_ref(v_env_2850_);
lean_dec(v_declName_2836_);
return v___x_2879_;
}
}
}
}
v___jp_2847_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
v___jp_2851_:
{
lean_object* v___x_2853_; size_t v_sz_2854_; size_t v___x_2855_; lean_object* v___x_2856_; 
v___x_2853_ = lean_box(0);
v_sz_2854_ = lean_array_size(v___y_2852_);
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2850_, v_declName_2836_, v___y_2852_, v_sz_2854_, v___x_2855_, v___x_2853_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___y_2852_);
lean_dec_ref(v_env_2850_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v___x_2856_, 0);
lean_dec(v_unused_2864_);
v___x_2858_ = v___x_2856_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v___x_2856_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2853_);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2853_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
else
{
return v___x_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2889_, lean_object* v_isMeta_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v_isMeta_boxed_2899_; lean_object* v_res_2900_; 
v_isMeta_boxed_2899_ = lean_unbox(v_isMeta_2890_);
v_res_2900_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2889_, v_isMeta_boxed_2899_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2901_, lean_object* v_b_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
if (lean_obj_tag(v_as_x27_2901_) == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_b_2902_);
return v___x_2911_;
}
else
{
lean_object* v_head_2912_; lean_object* v_tail_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; 
v_head_2912_ = lean_ctor_get(v_as_x27_2901_, 0);
v_tail_2913_ = lean_ctor_get(v_as_x27_2901_, 1);
v___x_2914_ = 1;
lean_inc(v_head_2912_);
v___x_2915_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2912_, v___x_2914_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2916_; 
lean_dec_ref_known(v___x_2915_, 1);
v___x_2916_ = lean_box(0);
v_as_x27_2901_ = v_tail_2913_;
v_b_2902_ = v___x_2916_;
goto _start;
}
else
{
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2918_, lean_object* v_b_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2918_, v_b_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v_as_x27_2918_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2929_, lean_object* v_options_2930_, lean_object* v_currNamespace_2931_, lean_object* v_openDecls_2932_, lean_object* v_n_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = l_Lean_ResolveName_resolveGlobalName(v_env_2929_, v_options_2930_, v_currNamespace_2931_, v_openDecls_2932_, v_n_2933_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___y_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2938_, lean_object* v_options_2939_, lean_object* v_currNamespace_2940_, lean_object* v_openDecls_2941_, lean_object* v_n_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2938_, v_options_2939_, v_currNamespace_2940_, v_openDecls_2941_, v_n_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v_options_2939_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_2946_, lean_object* v_msg_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_toCold_2953_; lean_object* v_options_2954_; lean_object* v_currRecDepth_2955_; lean_object* v_maxRecDepth_2956_; lean_object* v_ref_2957_; lean_object* v_currNamespace_2958_; lean_object* v_openDecls_2959_; lean_object* v_initHeartbeats_2960_; lean_object* v_maxHeartbeats_2961_; lean_object* v_currMacroScope_2962_; uint8_t v_diag_2963_; uint8_t v_suppressElabErrors_2964_; lean_object* v_ref_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_toCold_2953_ = lean_ctor_get(v___y_2950_, 0);
v_options_2954_ = lean_ctor_get(v___y_2950_, 1);
v_currRecDepth_2955_ = lean_ctor_get(v___y_2950_, 2);
v_maxRecDepth_2956_ = lean_ctor_get(v___y_2950_, 3);
v_ref_2957_ = lean_ctor_get(v___y_2950_, 4);
v_currNamespace_2958_ = lean_ctor_get(v___y_2950_, 5);
v_openDecls_2959_ = lean_ctor_get(v___y_2950_, 6);
v_initHeartbeats_2960_ = lean_ctor_get(v___y_2950_, 7);
v_maxHeartbeats_2961_ = lean_ctor_get(v___y_2950_, 8);
v_currMacroScope_2962_ = lean_ctor_get(v___y_2950_, 9);
v_diag_2963_ = lean_ctor_get_uint8(v___y_2950_, sizeof(void*)*10);
v_suppressElabErrors_2964_ = lean_ctor_get_uint8(v___y_2950_, sizeof(void*)*10 + 1);
v_ref_2965_ = l_Lean_replaceRef(v_ref_2946_, v_ref_2957_);
lean_inc(v_currMacroScope_2962_);
lean_inc(v_maxHeartbeats_2961_);
lean_inc(v_initHeartbeats_2960_);
lean_inc(v_openDecls_2959_);
lean_inc(v_currNamespace_2958_);
lean_inc(v_maxRecDepth_2956_);
lean_inc(v_currRecDepth_2955_);
lean_inc_ref(v_options_2954_);
lean_inc_ref(v_toCold_2953_);
v___x_2966_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2966_, 0, v_toCold_2953_);
lean_ctor_set(v___x_2966_, 1, v_options_2954_);
lean_ctor_set(v___x_2966_, 2, v_currRecDepth_2955_);
lean_ctor_set(v___x_2966_, 3, v_maxRecDepth_2956_);
lean_ctor_set(v___x_2966_, 4, v_ref_2965_);
lean_ctor_set(v___x_2966_, 5, v_currNamespace_2958_);
lean_ctor_set(v___x_2966_, 6, v_openDecls_2959_);
lean_ctor_set(v___x_2966_, 7, v_initHeartbeats_2960_);
lean_ctor_set(v___x_2966_, 8, v_maxHeartbeats_2961_);
lean_ctor_set(v___x_2966_, 9, v_currMacroScope_2962_);
lean_ctor_set_uint8(v___x_2966_, sizeof(void*)*10, v_diag_2963_);
lean_ctor_set_uint8(v___x_2966_, sizeof(void*)*10 + 1, v_suppressElabErrors_2964_);
v___x_2967_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_2947_, v___y_2948_, v___y_2949_, v___x_2966_, v___y_2951_);
lean_dec_ref_known(v___x_2966_, 10);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2968_, lean_object* v_msg_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_2968_, v_msg_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v_ref_2968_);
return v_res_2975_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l_Lean_maxRecDepthErrorMessage;
v___x_2982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_2984_ = l_Lean_MessageData_ofFormat(v___x_2983_);
return v___x_2984_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_2986_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_2987_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v___x_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_2988_){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_ref_2988_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_2993_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v_toCold_3007_; lean_object* v_env_3008_; lean_object* v_options_3009_; lean_object* v_currRecDepth_3010_; lean_object* v_maxRecDepth_3011_; lean_object* v_ref_3012_; lean_object* v_currNamespace_3013_; lean_object* v_openDecls_3014_; lean_object* v_currMacroScope_3015_; lean_object* v_quotContext_3016_; lean_object* v___x_3017_; lean_object* v_nextMacroScope_3018_; lean_object* v___f_3019_; lean_object* v___f_3020_; lean_object* v___f_3021_; lean_object* v___f_3022_; lean_object* v___f_3023_; lean_object* v_methods_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3006_ = lean_st_ref_get(v___y_3004_);
v_toCold_3007_ = lean_ctor_get(v___y_3003_, 0);
v_env_3008_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref_n(v_env_3008_, 4);
lean_dec(v___x_3006_);
v_options_3009_ = lean_ctor_get(v___y_3003_, 1);
v_currRecDepth_3010_ = lean_ctor_get(v___y_3003_, 2);
v_maxRecDepth_3011_ = lean_ctor_get(v___y_3003_, 3);
v_ref_3012_ = lean_ctor_get(v___y_3003_, 4);
v_currNamespace_3013_ = lean_ctor_get(v___y_3003_, 5);
v_openDecls_3014_ = lean_ctor_get(v___y_3003_, 6);
v_currMacroScope_3015_ = lean_ctor_get(v___y_3003_, 9);
v_quotContext_3016_ = lean_ctor_get(v_toCold_3007_, 2);
v___x_3017_ = lean_st_ref_get(v___y_3004_);
v_nextMacroScope_3018_ = lean_ctor_get(v___x_3017_, 1);
lean_inc(v_nextMacroScope_3018_);
lean_dec(v___x_3017_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3019_, 0, v_env_3008_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3020_, 0, v_env_3008_);
lean_inc_n(v_openDecls_3014_, 2);
lean_inc_n(v_currNamespace_3013_, 3);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3021_, 0, v_env_3008_);
lean_closure_set(v___f_3021_, 1, v_currNamespace_3013_);
lean_closure_set(v___f_3021_, 2, v_openDecls_3014_);
v___f_3022_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3022_, 0, v_currNamespace_3013_);
lean_inc_ref(v_options_3009_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3023_, 0, v_env_3008_);
lean_closure_set(v___f_3023_, 1, v_options_3009_);
lean_closure_set(v___f_3023_, 2, v_currNamespace_3013_);
lean_closure_set(v___f_3023_, 3, v_openDecls_3014_);
v_methods_3024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3024_, 0, v___f_3019_);
lean_ctor_set(v_methods_3024_, 1, v___f_3022_);
lean_ctor_set(v_methods_3024_, 2, v___f_3020_);
lean_ctor_set(v_methods_3024_, 3, v___f_3021_);
lean_ctor_set(v_methods_3024_, 4, v___f_3023_);
lean_inc(v_ref_3012_);
lean_inc(v_maxRecDepth_3011_);
lean_inc(v_currRecDepth_3010_);
lean_inc(v_currMacroScope_3015_);
lean_inc(v_quotContext_3016_);
v___x_3025_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3025_, 0, v_methods_3024_);
lean_ctor_set(v___x_3025_, 1, v_quotContext_3016_);
lean_ctor_set(v___x_3025_, 2, v_currMacroScope_3015_);
lean_ctor_set(v___x_3025_, 3, v_currRecDepth_3010_);
lean_ctor_set(v___x_3025_, 4, v_maxRecDepth_3011_);
lean_ctor_set(v___x_3025_, 5, v_ref_3012_);
v___x_3026_ = lean_box(0);
v___x_3027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3027_, 0, v_nextMacroScope_3018_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
lean_ctor_set(v___x_3027_, 2, v___x_3026_);
v___x_3028_ = lean_apply_2(v_x_2997_, v___x_3025_, v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v_a_3030_; lean_object* v_macroScope_3031_; lean_object* v_traceMsgs_3032_; lean_object* v_expandedMacroDecls_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_a_3029_);
v_a_3030_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3028_, 2);
v_macroScope_3031_ = lean_ctor_get(v_a_3029_, 0);
lean_inc(v_macroScope_3031_);
v_traceMsgs_3032_ = lean_ctor_get(v_a_3029_, 1);
lean_inc(v_traceMsgs_3032_);
v_expandedMacroDecls_3033_ = lean_ctor_get(v_a_3029_, 2);
lean_inc(v_expandedMacroDecls_3033_);
lean_dec(v_a_3029_);
v___x_3034_ = lean_box(0);
v___x_3035_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3033_, v___x_3034_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v_expandedMacroDecls_3033_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v___x_3036_; lean_object* v_env_3037_; lean_object* v_ngen_3038_; lean_object* v_auxDeclNGen_3039_; lean_object* v_traceState_3040_; lean_object* v_cache_3041_; lean_object* v_messages_3042_; lean_object* v_infoState_3043_; lean_object* v_snapshotTasks_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = lean_st_ref_take(v___y_3004_);
v_env_3037_ = lean_ctor_get(v___x_3036_, 0);
v_ngen_3038_ = lean_ctor_get(v___x_3036_, 2);
v_auxDeclNGen_3039_ = lean_ctor_get(v___x_3036_, 3);
v_traceState_3040_ = lean_ctor_get(v___x_3036_, 4);
v_cache_3041_ = lean_ctor_get(v___x_3036_, 5);
v_messages_3042_ = lean_ctor_get(v___x_3036_, 6);
v_infoState_3043_ = lean_ctor_get(v___x_3036_, 7);
v_snapshotTasks_3044_ = lean_ctor_get(v___x_3036_, 8);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3036_, 1);
lean_dec(v_unused_3071_);
v___x_3046_ = v___x_3036_;
v_isShared_3047_ = v_isSharedCheck_3070_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_snapshotTasks_3044_);
lean_inc(v_infoState_3043_);
lean_inc(v_messages_3042_);
lean_inc(v_cache_3041_);
lean_inc(v_traceState_3040_);
lean_inc(v_auxDeclNGen_3039_);
lean_inc(v_ngen_3038_);
lean_inc(v_env_3037_);
lean_dec(v___x_3036_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3070_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 1, v_macroScope_3031_);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_env_3037_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_macroScope_3031_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_ngen_3038_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_auxDeclNGen_3039_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_traceState_3040_);
lean_ctor_set(v_reuseFailAlloc_3069_, 5, v_cache_3041_);
lean_ctor_set(v_reuseFailAlloc_3069_, 6, v_messages_3042_);
lean_ctor_set(v_reuseFailAlloc_3069_, 7, v_infoState_3043_);
lean_ctor_set(v_reuseFailAlloc_3069_, 8, v_snapshotTasks_3044_);
v___x_3049_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_st_ref_put(v___y_3004_, v___x_3049_);
v___x_3051_ = l_List_reverse___redArg(v_traceMsgs_3032_);
v___x_3052_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3051_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3060_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_a_3030_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3030_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_3030_);
v_a_3061_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3052_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3052_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_traceMsgs_3032_);
lean_dec(v_macroScope_3031_);
lean_dec(v_a_3030_);
v_a_3072_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3035_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3035_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3028_, 2);
if (lean_obj_tag(v_a_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_a_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v_a_3081_ = lean_ctor_get(v_a_3080_, 0);
lean_inc(v_a_3081_);
v_a_3082_ = lean_ctor_get(v_a_3080_, 1);
lean_inc_ref(v_a_3082_);
lean_dec_ref_known(v_a_3080_, 2);
v___x_3083_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3084_ = lean_string_dec_eq(v_a_3082_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3082_);
v___x_3086_ = l_Lean_MessageData_ofFormat(v___x_3085_);
v___x_3087_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3081_, v___x_3086_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v_a_3081_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
lean_dec_ref(v_a_3082_);
v___x_3088_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3081_);
return v___x_3088_;
}
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3091_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_toCold_3104_; lean_object* v_currMacroScope_3105_; lean_object* v_quotContext_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_toCold_3104_ = lean_ctor_get(v___y_3101_, 0);
lean_inc_ref(v_toCold_3104_);
v_currMacroScope_3105_ = lean_ctor_get(v___y_3101_, 9);
lean_inc(v_currMacroScope_3105_);
lean_dec_ref(v___y_3101_);
v_quotContext_3106_ = lean_ctor_get(v_toCold_3104_, 2);
lean_inc(v_quotContext_3106_);
lean_dec_ref(v_toCold_3104_);
v___x_3107_ = l_Lean_addMacroScope(v_quotContext_3106_, v___x_3100_, v_currMacroScope_3105_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v___f_3122_; lean_object* v___x_3123_; 
v___f_3122_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3123_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3122_, v___y_3119_, v___y_3120_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3128_, uint8_t v_canonical_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3147_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = l_Lean_mkIdentFrom(v_ref_3128_, v_a_3139_, v_canonical_3129_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3138_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3138_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3156_, lean_object* v_canonical_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v_canonical_boxed_3166_; lean_object* v_res_3167_; 
v_canonical_boxed_3166_ = lean_unbox(v_canonical_3157_);
v_res_3167_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3156_, v_canonical_boxed_3166_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v_ref_3156_);
return v_res_3167_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3180_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3181_ = l_Lean_Name_append(v___x_3180_, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3191_, lean_object* v_letOrReassign_3192_, lean_object* v_decl_3193_, lean_object* v_tk_3194_, lean_object* v_dec_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3191_, v_letOrReassign_3192_, v_decl_3193_, v_tk_3194_, v_dec_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec_ref(v_a_3196_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3205_, lean_object* v_letOrReassign_3206_, lean_object* v_decl_3207_, lean_object* v_tk_3208_, lean_object* v_dec_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3205_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3219_; 
lean_dec_ref_known(v___x_3218_, 1);
lean_inc(v_decl_3207_);
v___x_3219_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3207_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3206_, v_a_3220_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
lean_dec_ref_known(v___x_3221_, 1);
v___x_3222_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3209_, v_tk_3208_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3224_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v___x_3224_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3206_, v_decl_3207_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v_doBlockResultType_3226_; lean_object* v___x_3227_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_doBlockResultType_3226_ = lean_ctor_get(v_a_3210_, 3);
lean_inc_ref(v_doBlockResultType_3226_);
v___x_3227_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3226_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3454_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3454_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3454_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3232_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3233_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3234_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3225_);
v___x_3236_ = l_Lean_Syntax_isOfKind(v_a_3225_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
lean_dec(v_a_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_tk_3208_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v___x_3237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l_Lean_Syntax_getArg(v_a_3225_, v___x_3238_);
lean_dec(v_a_3225_);
v___x_3240_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3239_);
v___x_3241_ = l_Lean_Syntax_isOfKind(v___x_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; uint8_t v___x_3243_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v_id_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; 
lean_dec(v_tk_3208_);
v___x_3242_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3239_);
v___x_3243_ = l_Lean_Syntax_isOfKind(v___x_3239_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3239_);
v___x_3358_ = l_Lean_Syntax_isOfKind(v___x_3239_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec(v___x_3239_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v___x_3359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3359_;
}
else
{
goto v___jp_3340_;
}
}
else
{
goto v___jp_3340_;
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = l_Lean_Syntax_getArg(v___x_3239_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_matchesNull(v___x_3361_, v___x_3238_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_dec(v___x_3239_);
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v___x_3363_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v_rhs_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v_xType_x3f_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3364_ = lean_box(v___x_3241_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3365_, 0, v___x_3364_);
v___x_3366_ = l_Lean_Syntax_getArg(v___x_3239_, v___x_3238_);
v___x_3422_ = lean_unsigned_to_nat(2u);
v___x_3423_ = l_Lean_Syntax_getArg(v___x_3239_, v___x_3422_);
v___x_3424_ = l_Lean_Syntax_isNone(v___x_3423_);
if (v___x_3424_ == 0)
{
uint8_t v___x_3425_; 
lean_inc(v___x_3423_);
v___x_3425_ = l_Lean_Syntax_matchesNull(v___x_3423_, v___x_3360_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
lean_dec(v___x_3423_);
lean_dec(v___x_3366_);
lean_dec_ref(v___f_3365_);
lean_dec(v___x_3239_);
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v___x_3426_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3427_ = l_Lean_Syntax_getArg(v___x_3423_, v___x_3238_);
lean_dec(v___x_3423_);
v___x_3428_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3427_);
v___x_3429_ = l_Lean_Syntax_isOfKind(v___x_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v___x_3427_);
lean_dec(v___x_3366_);
lean_dec_ref(v___f_3365_);
lean_dec(v___x_3239_);
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v___x_3430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = l_Lean_Syntax_getArg(v___x_3427_, v___x_3360_);
lean_dec(v___x_3427_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 1);
lean_ctor_set(v___x_3230_, 0, v___x_3431_);
v___x_3433_ = v___x_3230_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
v_xType_x3f_3387_ = v___x_3433_;
v___y_3388_ = v_a_3210_;
v___y_3389_ = v_a_3211_;
v___y_3390_ = v_a_3212_;
v___y_3391_ = v_a_3213_;
v___y_3392_ = v_a_3214_;
v___y_3393_ = v_a_3215_;
v___y_3394_ = v_a_3216_;
goto v___jp_3386_;
}
}
}
}
else
{
lean_object* v___x_3435_; 
lean_dec(v___x_3423_);
lean_del_object(v___x_3230_);
v___x_3435_ = lean_box(0);
v_xType_x3f_3387_ = v___x_3435_;
v___y_3388_ = v_a_3210_;
v___y_3389_ = v_a_3211_;
v___y_3390_ = v_a_3212_;
v___y_3391_ = v_a_3213_;
v___y_3392_ = v_a_3214_;
v___y_3393_ = v_a_3215_;
v___y_3394_ = v_a_3216_;
goto v___jp_3386_;
}
v___jp_3367_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3376_ = lean_box(v___x_3241_);
v___x_3377_ = lean_box(v___x_3236_);
lean_inc(v___x_3366_);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3378_, 0, v_rhs_3368_);
lean_closure_set(v___f_3378_, 1, v___x_3376_);
lean_closure_set(v___f_3378_, 2, v_config_3205_);
lean_closure_set(v___f_3378_, 3, v_a_3228_);
lean_closure_set(v___f_3378_, 4, v___x_3377_);
lean_closure_set(v___f_3378_, 5, v___x_3232_);
lean_closure_set(v___f_3378_, 6, v___x_3233_);
lean_closure_set(v___f_3378_, 7, v___x_3234_);
lean_closure_set(v___f_3378_, 8, v___f_3365_);
lean_closure_set(v___f_3378_, 9, v___x_3366_);
v___x_3379_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3379_, 0, v_a_3223_);
v___x_3380_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3380_, 0, v_letOrReassign_3206_);
lean_closure_set(v___x_3380_, 1, v_a_3220_);
lean_closure_set(v___x_3380_, 2, v___x_3379_);
v___x_3381_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3382_ = l_Lean_MessageData_ofSyntax(v___x_3366_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3383_, v___x_3380_, v___f_3378_, v___x_3384_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3385_;
}
v___jp_3386_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_unsigned_to_nat(4u);
v___x_3396_ = l_Lean_Syntax_getArg(v___x_3239_, v___x_3395_);
lean_dec(v___x_3239_);
if (lean_obj_tag(v_xType_x3f_3387_) == 0)
{
v_rhs_3368_ = v___x_3396_;
v___y_3369_ = v___y_3388_;
v___y_3370_ = v___y_3389_;
v___y_3371_ = v___y_3390_;
v___y_3372_ = v___y_3391_;
v___y_3373_ = v___y_3392_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3394_;
goto v___jp_3367_;
}
else
{
lean_object* v_toCold_3397_; lean_object* v_val_3398_; lean_object* v_ref_3399_; lean_object* v_currMacroScope_3400_; lean_object* v_quotContext_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_toCold_3397_ = lean_ctor_get(v___y_3393_, 0);
v_val_3398_ = lean_ctor_get(v_xType_x3f_3387_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v_xType_x3f_3387_, 1);
v_ref_3399_ = lean_ctor_get(v___y_3393_, 4);
v_currMacroScope_3400_ = lean_ctor_get(v___y_3393_, 9);
v_quotContext_3401_ = lean_ctor_get(v_toCold_3397_, 2);
v___x_3402_ = l_Lean_SourceInfo_fromRef(v_ref_3399_, v___x_3241_);
v___x_3403_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3405_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3402_, 7);
v___x_3406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3402_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3408_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3409_ = lean_box(0);
lean_inc(v_currMacroScope_3400_);
lean_inc(v_quotContext_3401_);
v___x_3410_ = l_Lean_addMacroScope(v_quotContext_3401_, v___x_3409_, v_currMacroScope_3400_);
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3412_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3402_);
lean_ctor_set(v___x_3412_, 1, v___x_3408_);
lean_ctor_set(v___x_3412_, 2, v___x_3410_);
lean_ctor_set(v___x_3412_, 3, v___x_3411_);
v___x_3413_ = l_Lean_Syntax_node1(v___x_3402_, v___x_3407_, v___x_3412_);
v___x_3414_ = l_Lean_Syntax_node2(v___x_3402_, v___x_3404_, v___x_3406_, v___x_3413_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3402_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3418_ = l_Lean_Syntax_node1(v___x_3402_, v___x_3417_, v_val_3398_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3402_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_Syntax_node5(v___x_3402_, v___x_3403_, v___x_3414_, v___x_3396_, v___x_3416_, v___x_3418_, v___x_3420_);
v_rhs_3368_ = v___x_3421_;
v___y_3369_ = v___y_3388_;
v___y_3370_ = v___y_3389_;
v___y_3371_ = v___y_3390_;
v___y_3372_ = v___y_3391_;
v___y_3373_ = v___y_3392_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3394_;
goto v___jp_3367_;
}
}
}
}
v___jp_3244_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___f_3264_; lean_object* v___x_3265_; 
v___x_3261_ = lean_box(v___x_3236_);
v___x_3262_ = lean_box(v___x_3243_);
v___x_3263_ = lean_box(v___y_3260_);
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3264_, 0, v___y_3249_);
lean_closure_set(v___f_3264_, 1, v___y_3247_);
lean_closure_set(v___f_3264_, 2, v___x_3261_);
lean_closure_set(v___f_3264_, 3, v___x_3262_);
lean_closure_set(v___f_3264_, 4, v___x_3238_);
lean_closure_set(v___f_3264_, 5, v___x_3263_);
v___x_3265_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3258_, v___f_3264_, v___y_3256_, v___y_3255_, v___y_3259_, v___y_3251_, v___y_3252_, v___y_3254_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v_options_3267_; lean_object* v_fst_3268_; lean_object* v_snd_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3309_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v_options_3267_ = lean_ctor_get(v___y_3252_, 1);
v_fst_3268_ = lean_ctor_get(v_a_3266_, 0);
v_snd_3269_ = lean_ctor_get(v_a_3266_, 1);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_a_3266_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3271_ = v_a_3266_;
v_isShared_3272_ = v_isSharedCheck_3309_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_snd_3269_);
lean_inc(v_fst_3268_);
lean_dec(v_a_3266_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3309_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_toCold_3273_; uint8_t v_hasTrace_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; 
v_toCold_3273_ = lean_ctor_get(v___y_3252_, 0);
v_hasTrace_3274_ = lean_ctor_get_uint8(v_options_3267_, sizeof(void*)*1);
v___x_3275_ = lean_box(v___y_3246_);
v___x_3276_ = lean_box(v___y_3248_);
v___x_3277_ = lean_box(v___y_3260_);
v___x_3278_ = lean_box(v___x_3236_);
lean_inc(v_snd_3269_);
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 19, 10);
lean_closure_set(v___f_3279_, 0, v___y_3250_);
lean_closure_set(v___f_3279_, 1, v___y_3245_);
lean_closure_set(v___f_3279_, 2, v_a_3223_);
lean_closure_set(v___f_3279_, 3, v___x_3275_);
lean_closure_set(v___f_3279_, 4, v___x_3276_);
lean_closure_set(v___f_3279_, 5, v_snd_3269_);
lean_closure_set(v___f_3279_, 6, v___x_3277_);
lean_closure_set(v___f_3279_, 7, v___x_3278_);
lean_closure_set(v___f_3279_, 8, v_letOrReassign_3206_);
lean_closure_set(v___f_3279_, 9, v_a_3220_);
v___x_3280_ = l_Lean_Syntax_getId(v___y_3257_);
lean_dec(v___y_3257_);
v___x_3281_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3280_);
if (v_hasTrace_3274_ == 0)
{
lean_object* v___x_3282_; 
lean_del_object(v___x_3271_);
v___x_3282_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3280_, v_fst_3268_, v_snd_3269_, v___f_3279_, v___y_3260_, v___x_3281_, v___y_3253_, v___y_3256_, v___y_3255_, v___y_3259_, v___y_3251_, v___y_3252_, v___y_3254_);
return v___x_3282_;
}
else
{
lean_object* v_inheritedTraceOptions_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v_inheritedTraceOptions_3283_ = lean_ctor_get(v_toCold_3273_, 4);
v___x_3284_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3285_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3286_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3283_, v_options_3267_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_del_object(v___x_3271_);
v___x_3287_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3280_, v_fst_3268_, v_snd_3269_, v___f_3279_, v___y_3260_, v___x_3281_, v___y_3253_, v___y_3256_, v___y_3255_, v___y_3259_, v___y_3251_, v___y_3252_, v___y_3254_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
lean_inc(v___x_3280_);
v___x_3288_ = l_Lean_MessageData_ofName(v___x_3280_);
v___x_3289_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 7);
lean_ctor_set(v___x_3271_, 1, v___x_3289_);
lean_ctor_set(v___x_3271_, 0, v___x_3288_);
v___x_3291_ = v___x_3271_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_inc(v_fst_3268_);
v___x_3292_ = l_Lean_MessageData_ofExpr(v_fst_3268_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
lean_inc(v_snd_3269_);
v___x_3296_ = l_Lean_MessageData_ofExpr(v_snd_3269_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3284_, v___x_3297_, v___y_3259_, v___y_3251_, v___y_3252_, v___y_3254_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v___x_3299_; 
lean_dec_ref_known(v___x_3298_, 1);
v___x_3299_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3280_, v_fst_3268_, v_snd_3269_, v___f_3279_, v___y_3260_, v___x_3281_, v___y_3253_, v___y_3256_, v___y_3255_, v___y_3259_, v___y_3251_, v___y_3252_, v___y_3254_);
return v___x_3299_;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v___x_3280_);
lean_dec_ref(v___f_3279_);
lean_dec(v_snd_3269_);
lean_dec(v_fst_3268_);
v_a_3300_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3298_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
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
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v___y_3257_);
lean_dec(v___y_3250_);
lean_dec(v___y_3245_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
v_a_3310_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3265_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3265_);
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
v___jp_3318_:
{
uint8_t v_nondep_3330_; 
v_nondep_3330_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1);
if (v_nondep_3330_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3206_) == 1)
{
uint8_t v_usedOnly_3331_; uint8_t v_zeta_3332_; lean_object* v_eq_x3f_3333_; 
v_usedOnly_3331_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 1);
v_zeta_3332_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 2);
v_eq_x3f_3333_ = lean_ctor_get(v_config_3205_, 0);
lean_inc(v_eq_x3f_3333_);
lean_dec_ref(v_config_3205_);
lean_inc(v_id_3322_);
v___y_3245_ = v_eq_x3f_3333_;
v___y_3246_ = v_zeta_3332_;
v___y_3247_ = v___y_3319_;
v___y_3248_ = v_usedOnly_3331_;
v___y_3249_ = v___y_3320_;
v___y_3250_ = v_id_3322_;
v___y_3251_ = v___y_3327_;
v___y_3252_ = v___y_3328_;
v___y_3253_ = v___y_3323_;
v___y_3254_ = v___y_3329_;
v___y_3255_ = v___y_3325_;
v___y_3256_ = v___y_3324_;
v___y_3257_ = v_id_3322_;
v___y_3258_ = v___y_3321_;
v___y_3259_ = v___y_3326_;
v___y_3260_ = v___x_3236_;
goto v___jp_3244_;
}
else
{
uint8_t v_usedOnly_3334_; uint8_t v_zeta_3335_; lean_object* v_eq_x3f_3336_; 
v_usedOnly_3334_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 1);
v_zeta_3335_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 2);
v_eq_x3f_3336_ = lean_ctor_get(v_config_3205_, 0);
lean_inc(v_eq_x3f_3336_);
lean_dec_ref(v_config_3205_);
lean_inc(v_id_3322_);
v___y_3245_ = v_eq_x3f_3336_;
v___y_3246_ = v_zeta_3335_;
v___y_3247_ = v___y_3319_;
v___y_3248_ = v_usedOnly_3334_;
v___y_3249_ = v___y_3320_;
v___y_3250_ = v_id_3322_;
v___y_3251_ = v___y_3327_;
v___y_3252_ = v___y_3328_;
v___y_3253_ = v___y_3323_;
v___y_3254_ = v___y_3329_;
v___y_3255_ = v___y_3325_;
v___y_3256_ = v___y_3324_;
v___y_3257_ = v_id_3322_;
v___y_3258_ = v___y_3321_;
v___y_3259_ = v___y_3326_;
v___y_3260_ = v___x_3243_;
goto v___jp_3244_;
}
}
else
{
uint8_t v_usedOnly_3337_; uint8_t v_zeta_3338_; lean_object* v_eq_x3f_3339_; 
v_usedOnly_3337_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 1);
v_zeta_3338_ = lean_ctor_get_uint8(v_config_3205_, sizeof(void*)*1 + 2);
v_eq_x3f_3339_ = lean_ctor_get(v_config_3205_, 0);
lean_inc(v_eq_x3f_3339_);
lean_dec_ref(v_config_3205_);
lean_inc(v_id_3322_);
v___y_3245_ = v_eq_x3f_3339_;
v___y_3246_ = v_zeta_3338_;
v___y_3247_ = v___y_3319_;
v___y_3248_ = v_usedOnly_3337_;
v___y_3249_ = v___y_3320_;
v___y_3250_ = v_id_3322_;
v___y_3251_ = v___y_3327_;
v___y_3252_ = v___y_3328_;
v___y_3253_ = v___y_3323_;
v___y_3254_ = v___y_3329_;
v___y_3255_ = v___y_3325_;
v___y_3256_ = v___y_3324_;
v___y_3257_ = v_id_3322_;
v___y_3258_ = v___y_3321_;
v___y_3259_ = v___y_3326_;
v___y_3260_ = v___x_3236_;
goto v___jp_3244_;
}
}
v___jp_3340_:
{
lean_object* v___x_3341_; lean_object* v_id_3342_; lean_object* v_binders_3343_; lean_object* v_type_3344_; lean_object* v_value_3345_; uint8_t v___x_3346_; 
v___x_3341_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3239_);
lean_dec(v___x_3239_);
v_id_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_id_3342_);
v_binders_3343_ = lean_ctor_get(v___x_3341_, 1);
lean_inc_ref(v_binders_3343_);
v_type_3344_ = lean_ctor_get(v___x_3341_, 2);
lean_inc(v_type_3344_);
v_value_3345_ = lean_ctor_get(v___x_3341_, 3);
lean_inc(v_value_3345_);
lean_dec_ref(v___x_3341_);
v___x_3346_ = l_Lean_Syntax_isIdent(v_id_3342_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3342_, v___x_3236_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_id_3342_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___y_3319_ = v_value_3345_;
v___y_3320_ = v_type_3344_;
v___y_3321_ = v_binders_3343_;
v_id_3322_ = v_a_3348_;
v___y_3323_ = v_a_3210_;
v___y_3324_ = v_a_3211_;
v___y_3325_ = v_a_3212_;
v___y_3326_ = v_a_3213_;
v___y_3327_ = v_a_3214_;
v___y_3328_ = v_a_3215_;
v___y_3329_ = v_a_3216_;
goto v___jp_3318_;
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_value_3345_);
lean_dec(v_type_3344_);
lean_dec_ref(v_binders_3343_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3349_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3347_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
v___y_3319_ = v_value_3345_;
v___y_3320_ = v_type_3344_;
v___y_3321_ = v_binders_3343_;
v_id_3322_ = v_id_3342_;
v___y_3323_ = v_a_3210_;
v___y_3324_ = v_a_3211_;
v___y_3325_ = v_a_3212_;
v___y_3326_ = v_a_3213_;
v___y_3327_ = v_a_3214_;
v___y_3328_ = v_a_3215_;
v___y_3329_ = v_a_3216_;
goto v___jp_3318_;
}
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_del_object(v___x_3230_);
lean_dec(v_a_3228_);
lean_dec(v_a_3220_);
v___x_3436_ = lean_box(v___x_3236_);
lean_inc(v___x_3239_);
v___x_3437_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3437_, 0, v___x_3239_);
lean_closure_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3437_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v_ref_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v_ref_3440_ = lean_ctor_get(v_a_3215_, 4);
v___x_3441_ = 0;
v___x_3442_ = l_Lean_SourceInfo_fromRef(v_ref_3440_, v___x_3441_);
v___x_3443_ = l_Lean_Syntax_node1(v___x_3442_, v___x_3235_, v_a_3439_);
lean_inc(v___x_3443_);
v___x_3444_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3444_, 0, v_config_3205_);
lean_closure_set(v___x_3444_, 1, v_letOrReassign_3206_);
lean_closure_set(v___x_3444_, 2, v___x_3443_);
lean_closure_set(v___x_3444_, 3, v_tk_3208_);
lean_closure_set(v___x_3444_, 4, v_a_3223_);
v___x_3445_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3239_, v___x_3443_, v___x_3444_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3445_;
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v___x_3239_);
lean_dec(v_a_3223_);
lean_dec(v_tk_3208_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3446_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3438_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3438_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3225_);
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_tk_3208_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
return v___x_3227_;
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v_a_3223_);
lean_dec(v_a_3220_);
lean_dec(v_tk_3208_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3455_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3224_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3224_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3220_);
lean_dec(v_tk_3208_);
lean_dec(v_decl_3207_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3463_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3222_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3222_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_a_3220_);
lean_dec_ref(v_dec_3209_);
lean_dec(v_tk_3208_);
lean_dec(v_decl_3207_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3471_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3221_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3221_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v_dec_3209_);
lean_dec(v_tk_3208_);
lean_dec(v_decl_3207_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3479_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3219_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3219_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v_dec_3209_);
lean_dec(v_tk_3208_);
lean_dec(v_decl_3207_);
lean_dec(v_letOrReassign_3206_);
lean_dec_ref(v_config_3205_);
v_a_3487_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3218_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3218_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3496_, v_x_3497_, v_x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3500_, lean_object* v_msg_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3500_, v_msg_3501_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3511_, lean_object* v_msg_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3511_, v_msg_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3527_, v___y_3528_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3540_, lean_object* v_beforeStx_3541_, lean_object* v_afterStx_3542_, lean_object* v_x_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3541_, v_afterStx_3542_, v_x_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3553_, lean_object* v_beforeStx_3554_, lean_object* v_afterStx_3555_, lean_object* v_x_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3553_, v_beforeStx_3554_, v_afterStx_3555_, v_x_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3567_, v___y_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3571_, lean_object* v_x_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3571_, v_x_3572_, v___y_3573_, v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v_x_3572_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3576_, lean_object* v_ref_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3577_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3587_, lean_object* v_ref_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3587_, v_ref_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3598_, lean_object* v_x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3609_, v_x_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, size_t v_x_3622_, size_t v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3621_, v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
size_t v_x_90133__boxed_3633_; size_t v_x_90134__boxed_3634_; lean_object* v_res_3635_; 
v_x_90133__boxed_3633_ = lean_unbox_usize(v_x_3629_);
lean_dec(v_x_3629_);
v_x_90134__boxed_3634_ = lean_unbox_usize(v_x_3630_);
lean_dec(v_x_3630_);
v_res_3635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3627_, v_x_3628_, v_x_90133__boxed_3633_, v_x_90134__boxed_3634_, v_x_3631_, v_x_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3636_, lean_object* v_stx_3637_, lean_object* v_output_3638_, lean_object* v_x_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3637_, v_output_3638_, v_x_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3648_, lean_object* v_stx_3649_, lean_object* v_output_3650_, lean_object* v_x_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3648_, v_stx_3649_, v_output_3650_, v_x_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3660_, lean_object* v_as_x27_3661_, lean_object* v_b_3662_, lean_object* v_a_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3661_, v_b_3662_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3673_, lean_object* v_as_x27_3674_, lean_object* v_b_3675_, lean_object* v_a_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3673_, v_as_x27_3674_, v_b_3675_, v_a_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v_as_x27_3674_);
lean_dec(v_as_3673_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3686_, lean_object* v_ref_3687_, lean_object* v_msg_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3687_, v_msg_3688_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3698_, lean_object* v_ref_3699_, lean_object* v_msg_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3698_, v_ref_3699_, v_msg_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v_ref_3699_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3710_, lean_object* v_n_3711_, lean_object* v_k_3712_, lean_object* v_v_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3711_, v_k_3712_, v_v_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3715_, size_t v_depth_3716_, lean_object* v_keys_3717_, lean_object* v_vals_3718_, lean_object* v_heq_3719_, lean_object* v_i_3720_, lean_object* v_entries_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3716_, v_keys_3717_, v_vals_3718_, v_i_3720_, v_entries_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3723_, lean_object* v_depth_3724_, lean_object* v_keys_3725_, lean_object* v_vals_3726_, lean_object* v_heq_3727_, lean_object* v_i_3728_, lean_object* v_entries_3729_){
_start:
{
size_t v_depth_boxed_3730_; lean_object* v_res_3731_; 
v_depth_boxed_3730_ = lean_unbox_usize(v_depth_3724_);
lean_dec(v_depth_3724_);
v_res_3731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3723_, v_depth_boxed_3730_, v_keys_3725_, v_vals_3726_, v_heq_3727_, v_i_3728_, v_entries_3729_);
lean_dec_ref(v_vals_3726_);
lean_dec_ref(v_keys_3725_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3748_, lean_object* v_x_3749_, lean_object* v_mkInfoTree_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3749_, v_mkInfoTree_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3759_, lean_object* v_x_3760_, lean_object* v_mkInfoTree_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3759_, v_x_3760_, v_mkInfoTree_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3770_, lean_object* v_m_3771_, lean_object* v_a_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3771_, v_a_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3774_, lean_object* v_m_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3774_, v_m_3775_, v_a_3776_);
lean_dec(v_a_3776_);
lean_dec_ref(v_m_3775_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3778_, lean_object* v_x_3779_, lean_object* v_x_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3779_, v_x_3780_, v_x_3781_, v_x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
uint8_t v___x_3787_; 
v___x_3787_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3785_, v_x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3788_, lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
uint8_t v_res_3791_; lean_object* v_r_3792_; 
v_res_3791_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3788_, v_x_3789_, v_x_3790_);
lean_dec_ref(v_x_3790_);
lean_dec_ref(v_x_3789_);
v_r_3792_ = lean_box(v_res_3791_);
return v_r_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3793_, lean_object* v_a_3794_, lean_object* v_x_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_3794_, v_x_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3797_, lean_object* v_a_3798_, lean_object* v_x_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3797_, v_a_3798_, v_x_3799_);
lean_dec(v_x_3799_);
lean_dec(v_a_3798_);
return v_res_3800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3801_, lean_object* v_x_3802_, size_t v_x_3803_, lean_object* v_x_3804_){
_start:
{
uint8_t v___x_3805_; 
v___x_3805_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3802_, v_x_3803_, v_x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3806_, lean_object* v_x_3807_, lean_object* v_x_3808_, lean_object* v_x_3809_){
_start:
{
size_t v_x_90303__boxed_3810_; uint8_t v_res_3811_; lean_object* v_r_3812_; 
v_x_90303__boxed_3810_ = lean_unbox_usize(v_x_3808_);
lean_dec(v_x_3808_);
v_res_3811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3806_, v_x_3807_, v_x_90303__boxed_3810_, v_x_3809_);
lean_dec_ref(v_x_3809_);
lean_dec_ref(v_x_3807_);
v_r_3812_ = lean_box(v_res_3811_);
return v_r_3812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3813_, lean_object* v_keys_3814_, lean_object* v_vals_3815_, lean_object* v_heq_3816_, lean_object* v_i_3817_, lean_object* v_k_3818_){
_start:
{
uint8_t v___x_3819_; 
v___x_3819_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3814_, v_i_3817_, v_k_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3820_, lean_object* v_keys_3821_, lean_object* v_vals_3822_, lean_object* v_heq_3823_, lean_object* v_i_3824_, lean_object* v_k_3825_){
_start:
{
uint8_t v_res_3826_; lean_object* v_r_3827_; 
v_res_3826_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3820_, v_keys_3821_, v_vals_3822_, v_heq_3823_, v_i_3824_, v_k_3825_);
lean_dec_ref(v_k_3825_);
lean_dec_ref(v_vals_3822_);
lean_dec_ref(v_keys_3821_);
v_r_3827_ = lean_box(v_res_3826_);
return v_r_3827_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3837_, lean_object* v_otherwise_x3f_3838_, uint8_t v___x_3839_, lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v___x_3842_, lean_object* v___x_3843_, lean_object* v___x_3844_, lean_object* v_dec_3845_, uint8_t v___x_3846_, lean_object* v___y_3847_, lean_object* v___x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; uint8_t v___y_3880_; 
switch(lean_obj_tag(v_letOrReassign_3837_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3838_) == 1)
{
lean_object* v_mutTk_x3f_3891_; lean_object* v_val_3892_; lean_object* v_ref_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3923_; 
v_mutTk_x3f_3891_ = lean_ctor_get(v_letOrReassign_3837_, 0);
v_val_3892_ = lean_ctor_get(v_otherwise_x3f_3838_, 0);
lean_inc(v_val_3892_);
lean_dec_ref_known(v_otherwise_x3f_3838_, 1);
v_ref_3893_ = lean_ctor_get(v___y_3854_, 4);
v___x_3894_ = l_Lean_SourceInfo_fromRef(v_ref_3893_, v___x_3839_);
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3896_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3895_);
v___x_3897_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3894_);
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3894_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3900_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3891_) == 1)
{
lean_object* v_val_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_val_3938_ = lean_ctor_get(v_mutTk_x3f_3891_, 0);
v___x_3939_ = l_Lean_SourceInfo_fromRef(v_val_3938_, v___x_3846_);
v___x_3940_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3939_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = l_Array_mkArray1___redArg(v___x_3941_);
v___y_3923_ = v___x_3942_;
goto v___jp_3922_;
}
else
{
lean_object* v___x_3943_; 
v___x_3943_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3923_ = v___x_3943_;
goto v___jp_3922_;
}
v___jp_3901_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3907_ = l_Array_append___redArg(v___x_3900_, v___y_3906_);
lean_dec_ref(v___y_3906_);
lean_inc(v___x_3894_);
v___x_3908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3894_);
lean_ctor_set(v___x_3908_, 1, v___x_3899_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
v___x_3909_ = lean_unsigned_to_nat(9u);
v___x_3910_ = lean_mk_empty_array_with_capacity(v___x_3909_);
v___x_3911_ = lean_array_push(v___x_3910_, v___x_3898_);
v___x_3912_ = lean_array_push(v___x_3911_, v___y_3905_);
v___x_3913_ = lean_array_push(v___x_3912_, v___y_3903_);
v___x_3914_ = lean_array_push(v___x_3913_, v___x_3843_);
v___x_3915_ = lean_array_push(v___x_3914_, v___y_3902_);
v___x_3916_ = lean_array_push(v___x_3915_, v___x_3844_);
v___x_3917_ = lean_array_push(v___x_3916_, v___y_3904_);
v___x_3918_ = lean_array_push(v___x_3917_, v_val_3892_);
v___x_3919_ = lean_array_push(v___x_3918_, v___x_3908_);
v___x_3920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3894_);
lean_ctor_set(v___x_3920_, 1, v___x_3896_);
lean_ctor_set(v___x_3920_, 2, v___x_3919_);
v___x_3921_ = l_Lean_Elab_Do_elabDoElem(v___x_3920_, v_dec_3845_, v___x_3846_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3921_;
}
v___jp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3924_ = l_Array_append___redArg(v___x_3900_, v___y_3923_);
lean_dec_ref(v___y_3923_);
lean_inc_n(v___x_3894_, 5);
v___x_3925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3894_);
lean_ctor_set(v___x_3925_, 1, v___x_3899_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3927_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3894_);
lean_ctor_set(v___x_3928_, 1, v___x_3899_);
lean_ctor_set(v___x_3928_, 2, v___x_3900_);
v___x_3929_ = l_Lean_Syntax_node1(v___x_3894_, v___x_3927_, v___x_3928_);
v___x_3930_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3894_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_3933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3894_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
if (lean_obj_tag(v___y_3847_) == 0)
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3902_ = v___x_3931_;
v___y_3903_ = v___x_3929_;
v___y_3904_ = v___x_3933_;
v___y_3905_ = v___x_3925_;
v___y_3906_ = v___x_3934_;
goto v___jp_3901_;
}
else
{
lean_object* v_val_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_val_3935_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v___y_3847_, 1);
v___x_3936_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___x_3937_ = lean_array_push(v___x_3936_, v_val_3935_);
v___y_3902_ = v___x_3931_;
v___y_3903_ = v___x_3929_;
v___y_3904_ = v___x_3933_;
v___y_3905_ = v___x_3925_;
v___y_3906_ = v___x_3937_;
goto v___jp_3901_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3944_; lean_object* v_ref_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___y_3954_; 
lean_dec(v___y_3847_);
lean_dec(v_otherwise_x3f_3838_);
v_mutTk_x3f_3944_ = lean_ctor_get(v_letOrReassign_3837_, 0);
v_ref_3945_ = lean_ctor_get(v___y_3854_, 4);
v___x_3946_ = l_Lean_SourceInfo_fromRef(v_ref_3945_, v___x_3839_);
v___x_3947_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3948_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3947_);
v___x_3949_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3946_);
v___x_3950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3946_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3952_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3944_) == 1)
{
lean_object* v_val_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_val_3971_ = lean_ctor_get(v_mutTk_x3f_3944_, 0);
v___x_3972_ = l_Lean_SourceInfo_fromRef(v_val_3971_, v___x_3846_);
v___x_3973_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Array_mkArray1___redArg(v___x_3974_);
v___y_3954_ = v___x_3975_;
goto v___jp_3953_;
}
else
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___y_3954_ = v___x_3976_;
goto v___jp_3953_;
}
v___jp_3953_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3955_ = l_Array_append___redArg(v___x_3952_, v___y_3954_);
lean_dec_ref(v___y_3954_);
lean_inc_n(v___x_3946_, 6);
v___x_3956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3946_);
lean_ctor_set(v___x_3956_, 1, v___x_3951_);
lean_ctor_set(v___x_3956_, 2, v___x_3955_);
v___x_3957_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3842_, 2);
lean_inc_ref_n(v___x_3841_, 2);
lean_inc_ref_n(v___x_3840_, 2);
v___x_3958_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3957_);
v___x_3959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3946_);
lean_ctor_set(v___x_3959_, 1, v___x_3951_);
lean_ctor_set(v___x_3959_, 2, v___x_3952_);
lean_inc_ref_n(v___x_3959_, 2);
v___x_3960_ = l_Lean_Syntax_node1(v___x_3946_, v___x_3958_, v___x_3959_);
v___x_3961_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3962_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3961_);
v___x_3963_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3964_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3963_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3946_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = l_Lean_Syntax_node5(v___x_3946_, v___x_3964_, v___x_3843_, v___x_3959_, v___x_3959_, v___x_3966_, v___x_3844_);
v___x_3968_ = l_Lean_Syntax_node1(v___x_3946_, v___x_3962_, v___x_3967_);
v___x_3969_ = l_Lean_Syntax_node4(v___x_3946_, v___x_3948_, v___x_3950_, v___x_3956_, v___x_3960_, v___x_3968_);
v___x_3970_ = l_Lean_Elab_Do_elabDoElem(v___x_3969_, v_dec_3845_, v___x_3846_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3970_;
}
}
}
case 1:
{
lean_dec(v___y_3847_);
if (lean_obj_tag(v_otherwise_x3f_3838_) == 1)
{
lean_object* v___x_3977_; 
lean_dec_ref_known(v_otherwise_x3f_3838_, 1);
lean_dec_ref(v_dec_3845_);
lean_dec(v___x_3844_);
lean_dec(v___x_3843_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v___x_3840_);
v___x_3977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3977_;
}
else
{
lean_object* v_ref_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec(v_otherwise_x3f_3838_);
v_ref_3978_ = lean_ctor_get(v___y_3854_, 4);
v___x_3979_ = l_Lean_SourceInfo_fromRef(v_ref_3978_, v___x_3839_);
v___x_3980_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3842_, 3);
lean_inc_ref_n(v___x_3841_, 3);
lean_inc_ref_n(v___x_3840_, 3);
v___x_3981_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3980_);
v___x_3982_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3979_, 6);
v___x_3983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3979_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3985_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3984_);
v___x_3986_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3987_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3979_);
lean_ctor_set(v___x_3988_, 1, v___x_3986_);
lean_ctor_set(v___x_3988_, 2, v___x_3987_);
lean_inc_ref_n(v___x_3988_, 2);
v___x_3989_ = l_Lean_Syntax_node1(v___x_3979_, v___x_3985_, v___x_3988_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3991_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3990_);
v___x_3992_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3993_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3992_);
v___x_3994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3979_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_Syntax_node5(v___x_3979_, v___x_3993_, v___x_3843_, v___x_3988_, v___x_3988_, v___x_3995_, v___x_3844_);
v___x_3997_ = l_Lean_Syntax_node1(v___x_3979_, v___x_3991_, v___x_3996_);
v___x_3998_ = l_Lean_Syntax_node3(v___x_3979_, v___x_3981_, v___x_3983_, v___x_3989_, v___x_3997_);
v___x_3999_ = l_Lean_Elab_Do_elabDoElem(v___x_3998_, v_dec_3845_, v___x_3846_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3999_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3838_);
if (lean_obj_tag(v___y_3847_) == 0)
{
v___y_3880_ = v___x_3846_;
goto v___jp_3879_;
}
else
{
lean_dec_ref_known(v___y_3847_, 1);
v___y_3880_ = v___x_3839_;
goto v___jp_3879_;
}
}
}
v___jp_3857_:
{
lean_object* v_ref_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_ref_3865_ = lean_ctor_get(v___y_3863_, 4);
v___x_3866_ = l_Lean_SourceInfo_fromRef(v_ref_3865_, v___x_3839_);
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3842_);
lean_inc_ref(v___x_3841_);
lean_inc_ref(v___x_3840_);
v___x_3868_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3867_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3870_ = l_Lean_Name_mkStr4(v___x_3840_, v___x_3841_, v___x_3842_, v___x_3869_);
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3872_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3866_, 3);
v___x_3873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3866_);
lean_ctor_set(v___x_3873_, 1, v___x_3871_);
lean_ctor_set(v___x_3873_, 2, v___x_3872_);
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3866_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
lean_inc_ref(v___x_3873_);
v___x_3876_ = l_Lean_Syntax_node5(v___x_3866_, v___x_3870_, v___x_3843_, v___x_3873_, v___x_3873_, v___x_3875_, v___x_3844_);
v___x_3877_ = l_Lean_Syntax_node1(v___x_3866_, v___x_3868_, v___x_3876_);
v___x_3878_ = l_Lean_Elab_Do_elabDoElem(v___x_3877_, v_dec_3845_, v___x_3846_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3878_;
}
v___jp_3879_:
{
if (v___y_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_dec_3845_);
lean_dec(v___x_3844_);
lean_dec(v___x_3843_);
lean_dec_ref(v___x_3842_);
lean_dec_ref(v___x_3841_);
lean_dec_ref(v___x_3840_);
v___x_3881_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3882_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_3881_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
v___y_3858_ = v___y_3849_;
v___y_3859_ = v___y_3850_;
v___y_3860_ = v___y_3851_;
v___y_3861_ = v___y_3852_;
v___y_3862_ = v___y_3853_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
goto v___jp_3857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4000_ = _args[0];
lean_object* v_otherwise_x3f_4001_ = _args[1];
lean_object* v___x_4002_ = _args[2];
lean_object* v___x_4003_ = _args[3];
lean_object* v___x_4004_ = _args[4];
lean_object* v___x_4005_ = _args[5];
lean_object* v___x_4006_ = _args[6];
lean_object* v___x_4007_ = _args[7];
lean_object* v_dec_4008_ = _args[8];
lean_object* v___x_4009_ = _args[9];
lean_object* v___y_4010_ = _args[10];
lean_object* v___x_4011_ = _args[11];
lean_object* v___y_4012_ = _args[12];
lean_object* v___y_4013_ = _args[13];
lean_object* v___y_4014_ = _args[14];
lean_object* v___y_4015_ = _args[15];
lean_object* v___y_4016_ = _args[16];
lean_object* v___y_4017_ = _args[17];
lean_object* v___y_4018_ = _args[18];
lean_object* v___y_4019_ = _args[19];
_start:
{
uint8_t v___x_30476__boxed_4020_; uint8_t v___x_30482__boxed_4021_; lean_object* v_res_4022_; 
v___x_30476__boxed_4020_ = lean_unbox(v___x_4002_);
v___x_30482__boxed_4021_ = lean_unbox(v___x_4009_);
v_res_4022_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4000_, v_otherwise_x3f_4001_, v___x_30476__boxed_4020_, v___x_4003_, v___x_4004_, v___x_4005_, v___x_4006_, v___x_4007_, v_dec_4008_, v___x_30482__boxed_4021_, v___y_4010_, v___x_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___x_4011_);
lean_dec(v_letOrReassign_4000_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4023_, lean_object* v_otherwise_x3f_4024_, uint8_t v___x_4025_, lean_object* v___x_4026_, lean_object* v___x_4027_, lean_object* v___x_4028_, lean_object* v___x_4029_, lean_object* v___x_4030_, lean_object* v_dec_4031_, uint8_t v___x_4032_, lean_object* v___y_4033_, lean_object* v___x_4034_, uint8_t v___x_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4067_; 
switch(lean_obj_tag(v_letOrReassign_4023_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4024_) == 1)
{
lean_object* v_mutTk_x3f_4078_; lean_object* v_val_4079_; lean_object* v_ref_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4110_; 
v_mutTk_x3f_4078_ = lean_ctor_get(v_letOrReassign_4023_, 0);
v_val_4079_ = lean_ctor_get(v_otherwise_x3f_4024_, 0);
lean_inc(v_val_4079_);
lean_dec_ref_known(v_otherwise_x3f_4024_, 1);
v_ref_4080_ = lean_ctor_get(v___y_4041_, 4);
v___x_4081_ = l_Lean_SourceInfo_fromRef(v_ref_4080_, v___x_4025_);
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4028_);
lean_inc_ref(v___x_4027_);
lean_inc_ref(v___x_4026_);
v___x_4083_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4082_);
v___x_4084_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4081_);
v___x_4085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4081_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4087_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4078_) == 1)
{
lean_object* v_val_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_val_4125_ = lean_ctor_get(v_mutTk_x3f_4078_, 0);
v___x_4126_ = l_Lean_SourceInfo_fromRef(v_val_4125_, v___x_4032_);
v___x_4127_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = l_Array_mkArray1___redArg(v___x_4128_);
v___y_4110_ = v___x_4129_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_mk_empty_array_with_capacity(v___x_4034_);
v___y_4110_ = v___x_4130_;
goto v___jp_4109_;
}
v___jp_4088_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4094_ = l_Array_append___redArg(v___x_4087_, v___y_4093_);
lean_dec_ref(v___y_4093_);
lean_inc(v___x_4081_);
v___x_4095_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4081_);
lean_ctor_set(v___x_4095_, 1, v___x_4086_);
lean_ctor_set(v___x_4095_, 2, v___x_4094_);
v___x_4096_ = lean_unsigned_to_nat(9u);
v___x_4097_ = lean_mk_empty_array_with_capacity(v___x_4096_);
v___x_4098_ = lean_array_push(v___x_4097_, v___x_4085_);
v___x_4099_ = lean_array_push(v___x_4098_, v___y_4092_);
v___x_4100_ = lean_array_push(v___x_4099_, v___y_4089_);
v___x_4101_ = lean_array_push(v___x_4100_, v___x_4029_);
v___x_4102_ = lean_array_push(v___x_4101_, v___y_4091_);
v___x_4103_ = lean_array_push(v___x_4102_, v___x_4030_);
v___x_4104_ = lean_array_push(v___x_4103_, v___y_4090_);
v___x_4105_ = lean_array_push(v___x_4104_, v_val_4079_);
v___x_4106_ = lean_array_push(v___x_4105_, v___x_4095_);
v___x_4107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4081_);
lean_ctor_set(v___x_4107_, 1, v___x_4083_);
lean_ctor_set(v___x_4107_, 2, v___x_4106_);
v___x_4108_ = l_Lean_Elab_Do_elabDoElem(v___x_4107_, v_dec_4031_, v___x_4032_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
return v___x_4108_;
}
v___jp_4109_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4111_ = l_Array_append___redArg(v___x_4087_, v___y_4110_);
lean_dec_ref(v___y_4110_);
lean_inc_n(v___x_4081_, 5);
v___x_4112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4081_);
lean_ctor_set(v___x_4112_, 1, v___x_4086_);
lean_ctor_set(v___x_4112_, 2, v___x_4111_);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4114_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4081_);
lean_ctor_set(v___x_4115_, 1, v___x_4086_);
lean_ctor_set(v___x_4115_, 2, v___x_4087_);
v___x_4116_ = l_Lean_Syntax_node1(v___x_4081_, v___x_4114_, v___x_4115_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4118_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4081_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4081_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
if (lean_obj_tag(v___y_4033_) == 0)
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_mk_empty_array_with_capacity(v___x_4034_);
v___y_4089_ = v___x_4116_;
v___y_4090_ = v___x_4120_;
v___y_4091_ = v___x_4118_;
v___y_4092_ = v___x_4112_;
v___y_4093_ = v___x_4121_;
goto v___jp_4088_;
}
else
{
lean_object* v_val_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_val_4122_ = lean_ctor_get(v___y_4033_, 0);
lean_inc(v_val_4122_);
lean_dec_ref_known(v___y_4033_, 1);
v___x_4123_ = lean_mk_empty_array_with_capacity(v___x_4034_);
v___x_4124_ = lean_array_push(v___x_4123_, v_val_4122_);
v___y_4089_ = v___x_4116_;
v___y_4090_ = v___x_4120_;
v___y_4091_ = v___x_4118_;
v___y_4092_ = v___x_4112_;
v___y_4093_ = v___x_4124_;
goto v___jp_4088_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4131_; lean_object* v_ref_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___y_4141_; 
lean_dec(v___y_4033_);
lean_dec(v_otherwise_x3f_4024_);
v_mutTk_x3f_4131_ = lean_ctor_get(v_letOrReassign_4023_, 0);
v_ref_4132_ = lean_ctor_get(v___y_4041_, 4);
v___x_4133_ = l_Lean_SourceInfo_fromRef(v_ref_4132_, v___x_4025_);
v___x_4134_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4028_);
lean_inc_ref(v___x_4027_);
lean_inc_ref(v___x_4026_);
v___x_4135_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4134_);
v___x_4136_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4133_);
v___x_4137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4133_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4139_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4131_) == 1)
{
lean_object* v_val_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_val_4158_ = lean_ctor_get(v_mutTk_x3f_4131_, 0);
v___x_4159_ = l_Lean_SourceInfo_fromRef(v_val_4158_, v___x_4032_);
v___x_4160_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Array_mkArray1___redArg(v___x_4161_);
v___y_4141_ = v___x_4162_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_mk_empty_array_with_capacity(v___x_4034_);
v___y_4141_ = v___x_4163_;
goto v___jp_4140_;
}
v___jp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4142_ = l_Array_append___redArg(v___x_4139_, v___y_4141_);
lean_dec_ref(v___y_4141_);
lean_inc_n(v___x_4133_, 6);
v___x_4143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4133_);
lean_ctor_set(v___x_4143_, 1, v___x_4138_);
lean_ctor_set(v___x_4143_, 2, v___x_4142_);
v___x_4144_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4028_, 2);
lean_inc_ref_n(v___x_4027_, 2);
lean_inc_ref_n(v___x_4026_, 2);
v___x_4145_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4144_);
v___x_4146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4133_);
lean_ctor_set(v___x_4146_, 1, v___x_4138_);
lean_ctor_set(v___x_4146_, 2, v___x_4139_);
lean_inc_ref_n(v___x_4146_, 2);
v___x_4147_ = l_Lean_Syntax_node1(v___x_4133_, v___x_4145_, v___x_4146_);
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4149_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4148_);
v___x_4150_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4151_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4150_);
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4133_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = l_Lean_Syntax_node5(v___x_4133_, v___x_4151_, v___x_4029_, v___x_4146_, v___x_4146_, v___x_4153_, v___x_4030_);
v___x_4155_ = l_Lean_Syntax_node1(v___x_4133_, v___x_4149_, v___x_4154_);
v___x_4156_ = l_Lean_Syntax_node4(v___x_4133_, v___x_4135_, v___x_4137_, v___x_4143_, v___x_4147_, v___x_4155_);
v___x_4157_ = l_Lean_Elab_Do_elabDoElem(v___x_4156_, v_dec_4031_, v___x_4032_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
return v___x_4157_;
}
}
}
case 1:
{
lean_dec(v___y_4033_);
if (lean_obj_tag(v_otherwise_x3f_4024_) == 1)
{
lean_object* v___x_4164_; 
lean_dec_ref_known(v_otherwise_x3f_4024_, 1);
lean_dec_ref(v_dec_4031_);
lean_dec(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec_ref(v___x_4028_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4026_);
v___x_4164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4164_;
}
else
{
lean_object* v_ref_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_dec(v_otherwise_x3f_4024_);
v_ref_4165_ = lean_ctor_get(v___y_4041_, 4);
v___x_4166_ = l_Lean_SourceInfo_fromRef(v_ref_4165_, v___x_4025_);
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4028_, 3);
lean_inc_ref_n(v___x_4027_, 3);
lean_inc_ref_n(v___x_4026_, 3);
v___x_4168_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4167_);
v___x_4169_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4166_, 6);
v___x_4170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4166_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4172_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4171_);
v___x_4173_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4174_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4166_);
lean_ctor_set(v___x_4175_, 1, v___x_4173_);
lean_ctor_set(v___x_4175_, 2, v___x_4174_);
lean_inc_ref_n(v___x_4175_, 2);
v___x_4176_ = l_Lean_Syntax_node1(v___x_4166_, v___x_4172_, v___x_4175_);
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4178_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4180_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4179_);
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4166_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l_Lean_Syntax_node5(v___x_4166_, v___x_4180_, v___x_4029_, v___x_4175_, v___x_4175_, v___x_4182_, v___x_4030_);
v___x_4184_ = l_Lean_Syntax_node1(v___x_4166_, v___x_4178_, v___x_4183_);
v___x_4185_ = l_Lean_Syntax_node3(v___x_4166_, v___x_4168_, v___x_4170_, v___x_4176_, v___x_4184_);
v___x_4186_ = l_Lean_Elab_Do_elabDoElem(v___x_4185_, v_dec_4031_, v___x_4032_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
return v___x_4186_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4024_);
if (lean_obj_tag(v___y_4033_) == 0)
{
v___y_4067_ = v___x_4035_;
goto v___jp_4066_;
}
else
{
lean_dec_ref_known(v___y_4033_, 1);
v___y_4067_ = v___x_4025_;
goto v___jp_4066_;
}
}
}
v___jp_4044_:
{
lean_object* v_ref_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_ref_4052_ = lean_ctor_get(v___y_4050_, 4);
v___x_4053_ = l_Lean_SourceInfo_fromRef(v_ref_4052_, v___x_4025_);
v___x_4054_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4028_);
lean_inc_ref(v___x_4027_);
lean_inc_ref(v___x_4026_);
v___x_4055_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4054_);
v___x_4056_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4057_ = l_Lean_Name_mkStr4(v___x_4026_, v___x_4027_, v___x_4028_, v___x_4056_);
v___x_4058_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4059_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4053_, 3);
v___x_4060_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4053_);
lean_ctor_set(v___x_4060_, 1, v___x_4058_);
lean_ctor_set(v___x_4060_, 2, v___x_4059_);
v___x_4061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4053_);
lean_ctor_set(v___x_4062_, 1, v___x_4061_);
lean_inc_ref(v___x_4060_);
v___x_4063_ = l_Lean_Syntax_node5(v___x_4053_, v___x_4057_, v___x_4029_, v___x_4060_, v___x_4060_, v___x_4062_, v___x_4030_);
v___x_4064_ = l_Lean_Syntax_node1(v___x_4053_, v___x_4055_, v___x_4063_);
v___x_4065_ = l_Lean_Elab_Do_elabDoElem(v___x_4064_, v_dec_4031_, v___x_4032_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4065_;
}
v___jp_4066_:
{
if (v___y_4067_ == 0)
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_dec_4031_);
lean_dec(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec_ref(v___x_4028_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4026_);
v___x_4068_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4069_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4068_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
else
{
v___y_4045_ = v___y_4036_;
v___y_4046_ = v___y_4037_;
v___y_4047_ = v___y_4038_;
v___y_4048_ = v___y_4039_;
v___y_4049_ = v___y_4040_;
v___y_4050_ = v___y_4041_;
v___y_4051_ = v___y_4042_;
goto v___jp_4044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4187_ = _args[0];
lean_object* v_otherwise_x3f_4188_ = _args[1];
lean_object* v___x_4189_ = _args[2];
lean_object* v___x_4190_ = _args[3];
lean_object* v___x_4191_ = _args[4];
lean_object* v___x_4192_ = _args[5];
lean_object* v___x_4193_ = _args[6];
lean_object* v___x_4194_ = _args[7];
lean_object* v_dec_4195_ = _args[8];
lean_object* v___x_4196_ = _args[9];
lean_object* v___y_4197_ = _args[10];
lean_object* v___x_4198_ = _args[11];
lean_object* v___x_4199_ = _args[12];
lean_object* v___y_4200_ = _args[13];
lean_object* v___y_4201_ = _args[14];
lean_object* v___y_4202_ = _args[15];
lean_object* v___y_4203_ = _args[16];
lean_object* v___y_4204_ = _args[17];
lean_object* v___y_4205_ = _args[18];
lean_object* v___y_4206_ = _args[19];
lean_object* v___y_4207_ = _args[20];
_start:
{
uint8_t v___x_30858__boxed_4208_; uint8_t v___x_30864__boxed_4209_; uint8_t v___x_30867__boxed_4210_; lean_object* v_res_4211_; 
v___x_30858__boxed_4208_ = lean_unbox(v___x_4189_);
v___x_30864__boxed_4209_ = lean_unbox(v___x_4196_);
v___x_30867__boxed_4210_ = lean_unbox(v___x_4199_);
v_res_4211_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4187_, v_otherwise_x3f_4188_, v___x_30858__boxed_4208_, v___x_4190_, v___x_4191_, v___x_4192_, v___x_4193_, v___x_4194_, v_dec_4195_, v___x_30864__boxed_4209_, v___y_4197_, v___x_4198_, v___x_30867__boxed_4210_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___x_4198_);
lean_dec(v_letOrReassign_4187_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4232_, lean_object* v_stx_4233_, lean_object* v_tk_4234_, lean_object* v_dec_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4245_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4247_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4233_);
v___x_4248_ = l_Lean_Syntax_isOfKind(v_stx_4233_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4233_);
v___x_4250_ = l_Lean_Syntax_isOfKind(v_stx_4233_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; 
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4251_;
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4252_);
v___x_4254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4253_);
v___x_4255_ = l_Lean_Syntax_isOfKind(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4341_; lean_object* v_patType_x3f_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4341_ = lean_unsigned_to_nat(1u);
v___x_4372_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4341_);
v___x_4373_ = l_Lean_Syntax_isNone(v___x_4372_);
if (v___x_4373_ == 0)
{
uint8_t v___x_4374_; 
lean_inc(v___x_4372_);
v___x_4374_ = l_Lean_Syntax_matchesNull(v___x_4372_, v___x_4341_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; 
lean_dec(v___x_4372_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4375_;
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4376_ = l_Lean_Syntax_getArg(v___x_4372_, v___x_4252_);
lean_dec(v___x_4372_);
v___x_4377_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4376_);
v___x_4378_ = l_Lean_Syntax_isOfKind(v___x_4376_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
lean_dec(v___x_4376_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4379_;
}
else
{
lean_object* v_patType_x3f_4380_; lean_object* v___x_4381_; 
v_patType_x3f_4380_ = l_Lean_Syntax_getArg(v___x_4376_, v___x_4341_);
lean_dec(v___x_4376_);
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_patType_x3f_4380_);
v_patType_x3f_4343_ = v___x_4381_;
v___y_4344_ = v_a_4236_;
v___y_4345_ = v_a_4237_;
v___y_4346_ = v_a_4238_;
v___y_4347_ = v_a_4239_;
v___y_4348_ = v_a_4240_;
v___y_4349_ = v_a_4241_;
v___y_4350_ = v_a_4242_;
goto v___jp_4342_;
}
}
}
else
{
lean_object* v___x_4382_; 
lean_dec(v___x_4372_);
v___x_4382_ = lean_box(0);
v_patType_x3f_4343_ = v___x_4382_;
v___y_4344_ = v_a_4236_;
v___y_4345_ = v_a_4237_;
v___y_4346_ = v_a_4238_;
v___y_4347_ = v_a_4239_;
v___y_4348_ = v_a_4240_;
v___y_4349_ = v_a_4241_;
v___y_4350_ = v_a_4242_;
goto v___jp_4342_;
}
v___jp_4342_:
{
lean_object* v___x_4351_; lean_object* v_rhs_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4351_ = lean_unsigned_to_nat(3u);
v_rhs_4352_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4351_);
v___x_4353_ = lean_unsigned_to_nat(4u);
v___x_4354_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4353_);
lean_dec(v_stx_4233_);
v___x_4355_ = l_Lean_Syntax_isNone(v___x_4354_);
if (v___x_4355_ == 0)
{
uint8_t v___x_4356_; 
lean_inc(v___x_4354_);
v___x_4356_ = l_Lean_Syntax_matchesNull(v___x_4354_, v___x_4351_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4357_; 
lean_dec(v___x_4354_);
lean_dec(v_rhs_4352_);
lean_dec(v_patType_x3f_4343_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_letOrReassign_4232_);
v___x_4357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4357_;
}
else
{
lean_object* v___x_4358_; lean_object* v_otherwise_x3f_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4359_ = l_Lean_Syntax_getArg(v___x_4354_, v___x_4341_);
v___x_4360_ = l_Lean_Syntax_getArg(v___x_4354_, v___x_4358_);
lean_dec(v___x_4354_);
v___x_4361_ = l_Lean_Syntax_getOptional_x3f(v___x_4360_);
lean_dec(v___x_4360_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_box(0);
v___y_4286_ = v___y_4348_;
v___y_4287_ = v_rhs_4352_;
v___y_4288_ = v___y_4344_;
v___y_4289_ = v_patType_x3f_4343_;
v___y_4290_ = v___y_4350_;
v___y_4291_ = v___y_4349_;
v___y_4292_ = v___y_4346_;
v___y_4293_ = v___y_4347_;
v___y_4294_ = v_otherwise_x3f_4359_;
v___y_4295_ = v___y_4345_;
v___y_4296_ = v___x_4362_;
goto v___jp_4285_;
}
else
{
lean_object* v_val_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
v_val_4363_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4361_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_val_4363_);
lean_dec(v___x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_val_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
v___y_4286_ = v___y_4348_;
v___y_4287_ = v_rhs_4352_;
v___y_4288_ = v___y_4344_;
v___y_4289_ = v_patType_x3f_4343_;
v___y_4290_ = v___y_4350_;
v___y_4291_ = v___y_4349_;
v___y_4292_ = v___y_4346_;
v___y_4293_ = v___y_4347_;
v___y_4294_ = v_otherwise_x3f_4359_;
v___y_4295_ = v___y_4345_;
v___y_4296_ = v___x_4368_;
goto v___jp_4285_;
}
}
}
}
}
else
{
lean_object* v___x_4371_; 
lean_dec(v___x_4354_);
v___x_4371_ = lean_box(0);
v___y_4257_ = v___y_4350_;
v___y_4258_ = v___y_4346_;
v___y_4259_ = v___y_4348_;
v___y_4260_ = v___y_4349_;
v___y_4261_ = v___y_4347_;
v___y_4262_ = v_patType_x3f_4343_;
v___y_4263_ = v___y_4345_;
v___y_4264_ = v_rhs_4352_;
v___y_4265_ = v___x_4371_;
v___y_4266_ = v___y_4344_;
v___y_4267_ = v___x_4371_;
goto v___jp_4256_;
}
}
}
else
{
lean_object* v_pattern_4383_; lean_object* v___x_4384_; lean_object* v_patType_x3f_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v_pattern_4383_ = l_Lean_Syntax_getArg(v___x_4253_, v___x_4252_);
v___x_4384_ = lean_unsigned_to_nat(1u);
v___x_4441_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4384_);
v___x_4442_ = l_Lean_Syntax_isNone(v___x_4441_);
if (v___x_4442_ == 0)
{
uint8_t v___x_4443_; 
lean_inc(v___x_4441_);
v___x_4443_ = l_Lean_Syntax_matchesNull(v___x_4441_, v___x_4384_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4444_; 
lean_dec(v___x_4441_);
lean_dec(v_pattern_4383_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4444_;
}
else
{
lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4445_ = l_Lean_Syntax_getArg(v___x_4441_, v___x_4252_);
lean_dec(v___x_4441_);
v___x_4446_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4445_);
v___x_4447_ = l_Lean_Syntax_isOfKind(v___x_4445_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; 
lean_dec(v___x_4445_);
lean_dec(v_pattern_4383_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4448_;
}
else
{
lean_object* v_patType_x3f_4449_; lean_object* v___x_4450_; 
v_patType_x3f_4449_ = l_Lean_Syntax_getArg(v___x_4445_, v___x_4384_);
lean_dec(v___x_4445_);
v___x_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4450_, 0, v_patType_x3f_4449_);
v_patType_x3f_4386_ = v___x_4450_;
v___y_4387_ = v_a_4236_;
v___y_4388_ = v_a_4237_;
v___y_4389_ = v_a_4238_;
v___y_4390_ = v_a_4239_;
v___y_4391_ = v_a_4240_;
v___y_4392_ = v_a_4241_;
v___y_4393_ = v_a_4242_;
goto v___jp_4385_;
}
}
}
else
{
lean_object* v___x_4451_; 
lean_dec(v___x_4441_);
v___x_4451_ = lean_box(0);
v_patType_x3f_4386_ = v___x_4451_;
v___y_4387_ = v_a_4236_;
v___y_4388_ = v_a_4237_;
v___y_4389_ = v_a_4238_;
v___y_4390_ = v_a_4239_;
v___y_4391_ = v_a_4240_;
v___y_4392_ = v_a_4241_;
v___y_4393_ = v_a_4242_;
goto v___jp_4385_;
}
v___jp_4385_:
{
lean_object* v___x_4394_; lean_object* v_rhs_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4394_ = lean_unsigned_to_nat(3u);
v_rhs_4395_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4394_);
v___x_4396_ = lean_unsigned_to_nat(4u);
v___x_4397_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4396_);
lean_dec(v_stx_4233_);
lean_inc(v___x_4397_);
v___x_4398_ = l_Lean_Syntax_matchesNull(v___x_4397_, v___x_4252_);
if (v___x_4398_ == 0)
{
uint8_t v___x_4399_; 
lean_dec(v_pattern_4383_);
v___x_4399_ = l_Lean_Syntax_isNone(v___x_4397_);
if (v___x_4399_ == 0)
{
uint8_t v___x_4400_; 
lean_inc(v___x_4397_);
v___x_4400_ = l_Lean_Syntax_matchesNull(v___x_4397_, v___x_4394_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; 
lean_dec(v___x_4397_);
lean_dec(v_rhs_4395_);
lean_dec(v_patType_x3f_4386_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_letOrReassign_4232_);
v___x_4401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4401_;
}
else
{
lean_object* v___x_4402_; lean_object* v_otherwise_x3f_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4402_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4403_ = l_Lean_Syntax_getArg(v___x_4397_, v___x_4384_);
v___x_4404_ = l_Lean_Syntax_getArg(v___x_4397_, v___x_4402_);
lean_dec(v___x_4397_);
v___x_4405_ = l_Lean_Syntax_getOptional_x3f(v___x_4404_);
lean_dec(v___x_4404_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4406_; 
v___x_4406_ = lean_box(0);
v___y_4329_ = v___y_4392_;
v___y_4330_ = v___y_4393_;
v___y_4331_ = v_patType_x3f_4386_;
v___y_4332_ = v___y_4390_;
v___y_4333_ = v___y_4391_;
v___y_4334_ = v___y_4388_;
v___y_4335_ = v___y_4387_;
v___y_4336_ = v_rhs_4395_;
v___y_4337_ = v___y_4389_;
v___y_4338_ = v_otherwise_x3f_4403_;
v___y_4339_ = v___x_4406_;
goto v___jp_4328_;
}
else
{
lean_object* v_val_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
v_val_4407_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4405_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_val_4407_);
lean_dec(v___x_4405_);
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
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
v___y_4329_ = v___y_4392_;
v___y_4330_ = v___y_4393_;
v___y_4331_ = v_patType_x3f_4386_;
v___y_4332_ = v___y_4390_;
v___y_4333_ = v___y_4391_;
v___y_4334_ = v___y_4388_;
v___y_4335_ = v___y_4387_;
v___y_4336_ = v_rhs_4395_;
v___y_4337_ = v___y_4389_;
v___y_4338_ = v_otherwise_x3f_4403_;
v___y_4339_ = v___x_4412_;
goto v___jp_4328_;
}
}
}
}
}
else
{
lean_object* v___x_4415_; 
lean_dec(v___x_4397_);
v___x_4415_ = lean_box(0);
v___y_4299_ = v___y_4393_;
v___y_4300_ = v___y_4391_;
v___y_4301_ = v_patType_x3f_4386_;
v___y_4302_ = v___y_4387_;
v___y_4303_ = v_rhs_4395_;
v___y_4304_ = v___y_4388_;
v___y_4305_ = v___x_4415_;
v___y_4306_ = v___y_4392_;
v___y_4307_ = v___y_4390_;
v___y_4308_ = v___y_4389_;
v___y_4309_ = v___x_4415_;
goto v___jp_4298_;
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
lean_dec(v___x_4397_);
lean_dec(v___x_4253_);
lean_dec(v_letOrReassign_4232_);
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4417_ = l_Lean_Core_mkFreshUserName(v___x_4416_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4235_, v_tk_4234_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; uint8_t v_kind_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v_kind_4421_ = lean_ctor_get_uint8(v_a_4420_, sizeof(void*)*3);
v___x_4422_ = l_Lean_mkIdentFrom(v_pattern_4383_, v_a_4418_, v___x_4248_);
lean_dec(v_pattern_4383_);
v___x_4423_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4423_, 0, v_a_4420_);
v___x_4424_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4422_, v_patType_x3f_4386_, v_rhs_4395_, v___x_4423_, v_kind_4421_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4424_;
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4418_);
lean_dec(v_rhs_4395_);
lean_dec(v_patType_x3f_4386_);
lean_dec(v_pattern_4383_);
v_a_4425_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4419_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4419_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_rhs_4395_);
lean_dec(v_patType_x3f_4386_);
lean_dec(v_pattern_4383_);
lean_dec_ref(v_dec_4235_);
v_a_4433_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4417_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4417_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
}
v___jp_4256_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4269_ = l_Lean_Core_mkFreshUserName(v___x_4268_, v___y_4260_, v___y_4257_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___y_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v___x_4271_ = l_Lean_mkIdentFrom(v___x_4253_, v_a_4270_, v___x_4255_);
v___x_4272_ = lean_box(v___x_4255_);
v___x_4273_ = lean_box(v___x_4250_);
lean_inc(v___x_4271_);
v___y_4274_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4274_, 0, v_letOrReassign_4232_);
lean_closure_set(v___y_4274_, 1, v___y_4265_);
lean_closure_set(v___y_4274_, 2, v___x_4272_);
lean_closure_set(v___y_4274_, 3, v___x_4244_);
lean_closure_set(v___y_4274_, 4, v___x_4245_);
lean_closure_set(v___y_4274_, 5, v___x_4246_);
lean_closure_set(v___y_4274_, 6, v___x_4253_);
lean_closure_set(v___y_4274_, 7, v___x_4271_);
lean_closure_set(v___y_4274_, 8, v_dec_4235_);
lean_closure_set(v___y_4274_, 9, v___x_4273_);
lean_closure_set(v___y_4274_, 10, v___y_4267_);
lean_closure_set(v___y_4274_, 11, v___x_4252_);
v___x_4275_ = 0;
v___x_4276_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4271_, v___y_4262_, v___y_4264_, v___y_4274_, v___x_4275_, v___y_4266_, v___y_4263_, v___y_4258_, v___y_4261_, v___y_4259_, v___y_4260_, v___y_4257_);
return v___x_4276_;
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v___y_4267_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec(v___y_4262_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_letOrReassign_4232_);
v_a_4277_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4269_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4269_);
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
v___jp_4285_:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___y_4294_);
v___y_4257_ = v___y_4290_;
v___y_4258_ = v___y_4292_;
v___y_4259_ = v___y_4286_;
v___y_4260_ = v___y_4291_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v___y_4289_;
v___y_4263_ = v___y_4295_;
v___y_4264_ = v___y_4287_;
v___y_4265_ = v___x_4297_;
v___y_4266_ = v___y_4288_;
v___y_4267_ = v___y_4296_;
goto v___jp_4256_;
}
v___jp_4298_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4311_ = l_Lean_Core_mkFreshUserName(v___x_4310_, v___y_4306_, v___y_4299_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___y_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = l_Lean_mkIdentFrom(v___x_4253_, v_a_4312_, v___x_4248_);
v___x_4314_ = lean_box(v___x_4248_);
v___x_4315_ = lean_box(v___x_4250_);
v___x_4316_ = lean_box(v___x_4255_);
lean_inc(v___x_4313_);
v___y_4317_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4317_, 0, v_letOrReassign_4232_);
lean_closure_set(v___y_4317_, 1, v___y_4305_);
lean_closure_set(v___y_4317_, 2, v___x_4314_);
lean_closure_set(v___y_4317_, 3, v___x_4244_);
lean_closure_set(v___y_4317_, 4, v___x_4245_);
lean_closure_set(v___y_4317_, 5, v___x_4246_);
lean_closure_set(v___y_4317_, 6, v___x_4253_);
lean_closure_set(v___y_4317_, 7, v___x_4313_);
lean_closure_set(v___y_4317_, 8, v_dec_4235_);
lean_closure_set(v___y_4317_, 9, v___x_4315_);
lean_closure_set(v___y_4317_, 10, v___y_4309_);
lean_closure_set(v___y_4317_, 11, v___x_4252_);
lean_closure_set(v___y_4317_, 12, v___x_4316_);
v___x_4318_ = 0;
v___x_4319_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4313_, v___y_4301_, v___y_4303_, v___y_4317_, v___x_4318_, v___y_4302_, v___y_4304_, v___y_4308_, v___y_4307_, v___y_4300_, v___y_4306_, v___y_4299_);
return v___x_4319_;
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v___y_4309_);
lean_dec(v___y_4305_);
lean_dec(v___y_4303_);
lean_dec(v___y_4301_);
lean_dec(v___x_4253_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_letOrReassign_4232_);
v_a_4320_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4311_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4311_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
v___jp_4328_:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___y_4338_);
v___y_4299_ = v___y_4330_;
v___y_4300_ = v___y_4333_;
v___y_4301_ = v___y_4331_;
v___y_4302_ = v___y_4335_;
v___y_4303_ = v___y_4336_;
v___y_4304_ = v___y_4334_;
v___y_4305_ = v___x_4340_;
v___y_4306_ = v___y_4329_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4337_;
v___y_4309_ = v___y_4339_;
goto v___jp_4298_;
}
}
}
else
{
lean_object* v___x_4452_; lean_object* v_x_4453_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v_xType_x3f_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v_xType_x3f_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4452_ = lean_unsigned_to_nat(0u);
v_x_4453_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4452_);
v___x_4526_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4453_);
v___x_4527_ = l_Lean_Syntax_isOfKind(v_x_4453_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; 
lean_dec(v_x_4453_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___x_4529_ = lean_unsigned_to_nat(1u);
v___x_4530_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4529_);
v___x_4531_ = l_Lean_Syntax_isNone(v___x_4530_);
if (v___x_4531_ == 0)
{
uint8_t v___x_4532_; 
lean_inc(v___x_4530_);
v___x_4532_ = l_Lean_Syntax_matchesNull(v___x_4530_, v___x_4529_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; 
lean_dec(v___x_4530_);
lean_dec(v_x_4453_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4533_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; 
v___x_4534_ = l_Lean_Syntax_getArg(v___x_4530_, v___x_4452_);
lean_dec(v___x_4530_);
v___x_4535_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4534_);
v___x_4536_ = l_Lean_Syntax_isOfKind(v___x_4534_, v___x_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_dec(v___x_4534_);
lean_dec(v_x_4453_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v___x_4537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4537_;
}
else
{
lean_object* v_xType_x3f_4538_; lean_object* v___x_4539_; 
v_xType_x3f_4538_ = l_Lean_Syntax_getArg(v___x_4534_, v___x_4529_);
lean_dec(v___x_4534_);
v___x_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_xType_x3f_4538_);
v_xType_x3f_4471_ = v___x_4539_;
v___y_4472_ = v_a_4236_;
v___y_4473_ = v_a_4237_;
v___y_4474_ = v_a_4238_;
v___y_4475_ = v_a_4239_;
v___y_4476_ = v_a_4240_;
v___y_4477_ = v_a_4241_;
v___y_4478_ = v_a_4242_;
goto v___jp_4470_;
}
}
}
else
{
lean_object* v___x_4540_; 
lean_dec(v___x_4530_);
v___x_4540_ = lean_box(0);
v_xType_x3f_4471_ = v___x_4540_;
v___y_4472_ = v_a_4236_;
v___y_4473_ = v_a_4237_;
v___y_4474_ = v_a_4238_;
v___y_4475_ = v_a_4239_;
v___y_4476_ = v_a_4240_;
v___y_4477_ = v_a_4241_;
v___y_4478_ = v_a_4242_;
goto v___jp_4470_;
}
}
v___jp_4454_:
{
uint8_t v_kind_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_kind_4465_ = lean_ctor_get_uint8(v___y_4456_, sizeof(void*)*3);
v___x_4466_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4232_);
lean_dec(v_letOrReassign_4232_);
v___x_4467_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4467_, 0, v___y_4456_);
lean_inc(v_x_4453_);
v___x_4468_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4468_, 0, lean_box(0));
lean_closure_set(v___x_4468_, 1, v___x_4466_);
lean_closure_set(v___x_4468_, 2, v_x_4453_);
lean_closure_set(v___x_4468_, 3, v___x_4467_);
v___x_4469_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4453_, v_xType_x3f_4457_, v___y_4455_, v___x_4468_, v_kind_4465_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v___x_4469_;
}
v___jp_4470_:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4479_ = lean_unsigned_to_nat(1u);
v___x_4480_ = lean_mk_empty_array_with_capacity(v___x_4479_);
lean_inc(v_x_4453_);
v___x_4481_ = lean_array_push(v___x_4480_, v_x_4453_);
v___x_4482_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4232_, v___x_4481_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec_ref(v___x_4481_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v___x_4483_; 
lean_dec_ref_known(v___x_4482_, 1);
v___x_4483_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4235_, v_tk_4234_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; lean_object* v_rhs_4486_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = lean_unsigned_to_nat(3u);
v_rhs_4486_ = l_Lean_Syntax_getArg(v_stx_4233_, v___x_4485_);
lean_dec(v_stx_4233_);
if (lean_obj_tag(v_letOrReassign_4232_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4471_) == 0)
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = l_Lean_TSyntax_getId(v_x_4453_);
v___x_4488_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4487_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = l_Lean_LocalDecl_type(v_a_4489_);
lean_dec(v_a_4489_);
v___x_4491_ = l_Lean_Elab_Term_exprToSyntax(v___x_4490_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4493_, 0, v_a_4492_);
v___y_4455_ = v_rhs_4486_;
v___y_4456_ = v_a_4484_;
v_xType_x3f_4457_ = v___x_4493_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4475_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
goto v___jp_4454_;
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_rhs_4486_);
lean_dec(v_a_4484_);
lean_dec(v_x_4453_);
v_a_4494_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4491_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4491_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_rhs_4486_);
lean_dec(v_a_4484_);
lean_dec(v_x_4453_);
v_a_4502_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4488_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4488_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
v___y_4455_ = v_rhs_4486_;
v___y_4456_ = v_a_4484_;
v_xType_x3f_4457_ = v_xType_x3f_4471_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4475_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
goto v___jp_4454_;
}
}
else
{
v___y_4455_ = v_rhs_4486_;
v___y_4456_ = v_a_4484_;
v_xType_x3f_4457_ = v_xType_x3f_4471_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4473_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4475_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
goto v___jp_4454_;
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v_xType_x3f_4471_);
lean_dec(v_x_4453_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v_a_4510_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4483_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4483_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_xType_x3f_4471_);
lean_dec(v_x_4453_);
lean_dec_ref(v_dec_4235_);
lean_dec(v_stx_4233_);
lean_dec(v_letOrReassign_4232_);
v_a_4518_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4482_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4482_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4541_, lean_object* v_stx_4542_, lean_object* v_tk_4543_, lean_object* v_dec_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4541_, v_stx_4542_, v_tk_4543_, v_dec_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_tk_4543_);
return v_res_4553_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4556_ = l_Lean_stringToMessageData(v___x_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4557_, lean_object* v_mutTk_x3f_4558_, lean_object* v_initConfig_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4558_) == 0)
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4557_, v_initConfig_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4567_;
}
else
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; uint8_t v___x_4572_; 
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = l_Lean_Syntax_getArg(v_letConfigStx_4557_, v___x_4568_);
v___x_4570_ = l_Lean_Syntax_getArgs(v___x_4569_);
lean_dec(v___x_4569_);
v___x_4571_ = lean_array_get_size(v___x_4570_);
lean_dec_ref(v___x_4570_);
v___x_4572_ = lean_nat_dec_eq(v___x_4571_, v___x_4568_);
if (v___x_4572_ == 0)
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec_ref(v_initConfig_4559_);
v___x_4573_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4574_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4557_, v___x_4573_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
lean_dec(v_letConfigStx_4557_);
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
else
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4557_, v_initConfig_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4584_, lean_object* v_mutTk_x3f_4585_, lean_object* v_initConfig_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4584_, v_mutTk_x3f_4585_, v_initConfig_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_mutTk_x3f_4585_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4595_, lean_object* v_mutTk_x3f_4596_, lean_object* v_initConfig_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4595_, v_mutTk_x3f_4596_, v_initConfig_4597_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4607_, lean_object* v_mutTk_x3f_4608_, lean_object* v_initConfig_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4607_, v_mutTk_x3f_4608_, v_initConfig_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_mutTk_x3f_4608_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4632_, lean_object* v_dec_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; uint8_t v___x_4643_; 
v___x_4642_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4632_);
v___x_4643_ = l_Lean_Syntax_isOfKind(v_stx_4632_, v___x_4642_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
lean_dec_ref(v_dec_4633_);
lean_dec(v_stx_4632_);
v___x_4644_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4644_;
}
else
{
lean_object* v___x_4645_; lean_object* v_tk_4646_; lean_object* v_mutTk_x3f_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4645_ = lean_unsigned_to_nat(0u);
v_tk_4646_ = l_Lean_Syntax_getArg(v_stx_4632_, v___x_4645_);
v___x_4679_ = lean_unsigned_to_nat(1u);
v___x_4680_ = l_Lean_Syntax_getArg(v_stx_4632_, v___x_4679_);
v___x_4681_ = l_Lean_Syntax_isNone(v___x_4680_);
if (v___x_4681_ == 0)
{
uint8_t v___x_4682_; 
lean_inc(v___x_4680_);
v___x_4682_ = l_Lean_Syntax_matchesNull(v___x_4680_, v___x_4679_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; 
lean_dec(v___x_4680_);
lean_dec(v_tk_4646_);
lean_dec_ref(v_dec_4633_);
lean_dec(v_stx_4632_);
v___x_4683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4683_;
}
else
{
lean_object* v_mutTk_x3f_4684_; lean_object* v___x_4685_; 
v_mutTk_x3f_4684_ = l_Lean_Syntax_getArg(v___x_4680_, v___x_4645_);
lean_dec(v___x_4680_);
v___x_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4685_, 0, v_mutTk_x3f_4684_);
v_mutTk_x3f_4648_ = v___x_4685_;
v___y_4649_ = v_a_4634_;
v___y_4650_ = v_a_4635_;
v___y_4651_ = v_a_4636_;
v___y_4652_ = v_a_4637_;
v___y_4653_ = v_a_4638_;
v___y_4654_ = v_a_4639_;
v___y_4655_ = v_a_4640_;
goto v___jp_4647_;
}
}
else
{
lean_object* v___x_4686_; 
lean_dec(v___x_4680_);
v___x_4686_ = lean_box(0);
v_mutTk_x3f_4648_ = v___x_4686_;
v___y_4649_ = v_a_4634_;
v___y_4650_ = v_a_4635_;
v___y_4651_ = v_a_4636_;
v___y_4652_ = v_a_4637_;
v___y_4653_ = v_a_4638_;
v___y_4654_ = v_a_4639_;
v___y_4655_ = v_a_4640_;
goto v___jp_4647_;
}
v___jp_4647_:
{
lean_object* v___x_4656_; lean_object* v_config_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4656_ = lean_unsigned_to_nat(2u);
v_config_4657_ = l_Lean_Syntax_getArg(v_stx_4632_, v___x_4656_);
v___x_4658_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4657_);
v___x_4659_ = l_Lean_Syntax_isOfKind(v_config_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; 
lean_dec(v_config_4657_);
lean_dec(v_mutTk_x3f_4648_);
lean_dec(v_tk_4646_);
lean_dec_ref(v_dec_4633_);
lean_dec(v_stx_4632_);
v___x_4660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v_decl_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(3u);
v_decl_4662_ = l_Lean_Syntax_getArg(v_stx_4632_, v___x_4661_);
lean_dec(v_stx_4632_);
v___x_4663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4662_);
v___x_4664_ = l_Lean_Syntax_isOfKind(v_decl_4662_, v___x_4663_);
if (v___x_4664_ == 0)
{
lean_object* v___x_4665_; 
lean_dec(v_decl_4662_);
lean_dec(v_config_4657_);
lean_dec(v_mutTk_x3f_4648_);
lean_dec(v_tk_4646_);
lean_dec_ref(v_dec_4633_);
v___x_4665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4665_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4667_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4657_, v_mutTk_x3f_4648_, v___x_4666_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v_mutTk_x3f_4648_);
v___x_4670_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4668_, v___x_4669_, v_decl_4662_, v_tk_4646_, v_dec_4633_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
return v___x_4670_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v_decl_4662_);
lean_dec(v_mutTk_x3f_4648_);
lean_dec(v_tk_4646_);
lean_dec_ref(v_dec_4633_);
v_a_4671_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4667_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4667_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4687_, lean_object* v_dec_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Elab_Do_elabDoLet(v_stx_4687_, v_dec_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec_ref(v_a_4689_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4705_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4706_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4707_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4708_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4709_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4705_, v___x_4706_, v___x_4707_, v___x_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4717_, lean_object* v_dec_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4717_);
v___x_4728_ = l_Lean_Syntax_isOfKind(v_stx_4717_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; 
lean_dec_ref(v_dec_4718_);
lean_dec(v_stx_4717_);
v___x_4729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4729_;
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4730_ = lean_unsigned_to_nat(1u);
v___x_4731_ = l_Lean_Syntax_getArg(v_stx_4717_, v___x_4730_);
v___x_4732_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4731_);
v___x_4733_ = l_Lean_Syntax_isOfKind(v___x_4731_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; 
lean_dec(v___x_4731_);
lean_dec_ref(v_dec_4718_);
lean_dec(v_stx_4717_);
v___x_4734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4734_;
}
else
{
lean_object* v___x_4735_; lean_object* v_decl_4736_; lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4735_ = lean_unsigned_to_nat(2u);
v_decl_4736_ = l_Lean_Syntax_getArg(v_stx_4717_, v___x_4735_);
v___x_4737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4736_);
v___x_4738_ = l_Lean_Syntax_isOfKind(v_decl_4736_, v___x_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
lean_dec(v_decl_4736_);
lean_dec(v___x_4731_);
lean_dec_ref(v_dec_4718_);
lean_dec(v_stx_4717_);
v___x_4739_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4739_;
}
else
{
uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4740_ = 0;
v___x_4741_ = lean_box(0);
v___x_4742_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*1, v___x_4738_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*1 + 1, v___x_4740_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*1 + 2, v___x_4740_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*1 + 3, v___x_4740_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*1 + 4, v___x_4740_);
v___x_4743_ = l_Lean_Elab_Term_mkLetConfig(v___x_4731_, v___x_4742_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4745_; lean_object* v_tk_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v___x_4743_, 1);
v___x_4745_ = lean_unsigned_to_nat(0u);
v_tk_4746_ = l_Lean_Syntax_getArg(v_stx_4717_, v___x_4745_);
lean_dec(v_stx_4717_);
v___x_4747_ = lean_box(1);
v___x_4748_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4744_, v___x_4747_, v_decl_4736_, v_tk_4746_, v_dec_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
return v___x_4748_;
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_dec(v_decl_4736_);
lean_dec_ref(v_dec_4718_);
lean_dec(v_stx_4717_);
v_a_4749_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4743_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4743_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4757_, lean_object* v_dec_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Elab_Do_elabDoHave(v_stx_4757_, v_dec_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec_ref(v_a_4759_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4775_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4776_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4777_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4778_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4779_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4775_, v___x_4776_, v___x_4777_, v___x_4778_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4784_, lean_object* v___x_4785_, lean_object* v___x_4786_, lean_object* v___x_4787_, lean_object* v_decls_4788_, lean_object* v_a_4789_, uint8_t v___x_4790_, lean_object* v_body_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_ref_4800_; uint8_t v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_ref_4800_ = lean_ctor_get(v___y_4797_, 4);
v___x_4801_ = 0;
v___x_4802_ = l_Lean_SourceInfo_fromRef(v_ref_4800_, v___x_4801_);
v___x_4803_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4804_ = l_Lean_Name_mkStr4(v___x_4784_, v___x_4785_, v___x_4786_, v___x_4803_);
v___x_4805_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4802_, 4);
v___x_4806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4802_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4802_);
lean_ctor_set(v___x_4808_, 1, v___x_4807_);
v___x_4809_ = l_Lean_Syntax_node2(v___x_4802_, v___x_4787_, v___x_4806_, v___x_4808_);
v___x_4810_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4802_);
lean_ctor_set(v___x_4811_, 1, v___x_4810_);
v___x_4812_ = l_Lean_Syntax_node4(v___x_4802_, v___x_4804_, v___x_4809_, v_decls_4788_, v___x_4811_, v_body_4791_);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_a_4789_);
v___x_4814_ = l_Lean_Elab_Term_elabTerm(v___x_4812_, v___x_4813_, v___x_4790_, v___x_4790_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4815_, lean_object* v___x_4816_, lean_object* v___x_4817_, lean_object* v___x_4818_, lean_object* v_decls_4819_, lean_object* v_a_4820_, lean_object* v___x_4821_, lean_object* v_body_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
uint8_t v___x_4485__boxed_4831_; lean_object* v_res_4832_; 
v___x_4485__boxed_4831_ = lean_unbox(v___x_4821_);
v_res_4832_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4815_, v___x_4816_, v___x_4817_, v___x_4818_, v_decls_4819_, v_a_4820_, v___x_4485__boxed_4831_, v_body_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec_ref(v___y_4823_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4833_, lean_object* v_a_4834_){
_start:
{
if (lean_obj_tag(v_a_4833_) == 0)
{
lean_object* v___x_4835_; 
v___x_4835_ = l_List_reverse___redArg(v_a_4834_);
return v___x_4835_;
}
else
{
lean_object* v_head_4836_; lean_object* v_tail_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4846_; 
v_head_4836_ = lean_ctor_get(v_a_4833_, 0);
v_tail_4837_ = lean_ctor_get(v_a_4833_, 1);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_a_4833_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4839_ = v_a_4833_;
v_isShared_4840_ = v_isSharedCheck_4846_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_tail_4837_);
lean_inc(v_head_4836_);
lean_dec(v_a_4833_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4846_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4841_; lean_object* v___x_4843_; 
v___x_4841_ = l_Lean_MessageData_ofSyntax(v_head_4836_);
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 1, v_a_4834_);
lean_ctor_set(v___x_4839_, 0, v___x_4841_);
v___x_4843_ = v___x_4839_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4841_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_a_4834_);
v___x_4843_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
v_a_4833_ = v_tail_4837_;
v_a_4834_ = v___x_4843_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4864_ = l_Lean_stringToMessageData(v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4865_, lean_object* v_dec_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4876_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4877_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4878_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4865_);
v___x_4879_ = l_Lean_Syntax_isOfKind(v_stx_4865_, v___x_4878_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; 
lean_dec_ref(v_dec_4866_);
lean_dec(v_stx_4865_);
v___x_4880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4880_;
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4881_ = lean_unsigned_to_nat(0u);
v___x_4882_ = l_Lean_Syntax_getArg(v_stx_4865_, v___x_4881_);
v___x_4883_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4882_);
v___x_4884_ = l_Lean_Syntax_isOfKind(v___x_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; 
lean_dec(v___x_4882_);
lean_dec_ref(v_dec_4866_);
lean_dec(v_stx_4865_);
v___x_4885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; lean_object* v_decls_4887_; lean_object* v___x_4888_; uint8_t v___x_4889_; 
v___x_4886_ = lean_unsigned_to_nat(1u);
v_decls_4887_ = l_Lean_Syntax_getArg(v_stx_4865_, v___x_4886_);
lean_dec(v_stx_4865_);
v___x_4888_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4887_);
v___x_4889_ = l_Lean_Syntax_isOfKind(v_decls_4887_, v___x_4888_);
if (v___x_4889_ == 0)
{
lean_object* v___x_4890_; 
lean_dec(v_decls_4887_);
lean_dec(v___x_4882_);
lean_dec_ref(v_dec_4866_);
v___x_4890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4890_;
}
else
{
lean_object* v_tk_4891_; lean_object* v___x_4892_; 
v_tk_4891_ = l_Lean_Syntax_getArg(v___x_4882_, v___x_4881_);
lean_dec(v___x_4882_);
v___x_4892_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4866_, v_tk_4891_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
lean_dec(v_tk_4891_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4894_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
lean_inc(v_decls_4887_);
v___x_4894_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4887_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v_doBlockResultType_4896_; lean_object* v___x_4897_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___x_4894_, 1);
v_doBlockResultType_4896_ = lean_ctor_get(v_a_4867_, 3);
lean_inc_ref(v_doBlockResultType_4896_);
v___x_4897_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4896_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4899_; lean_object* v___f_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref_known(v___x_4897_, 1);
v___x_4899_ = lean_box(v___x_4889_);
v___f_4900_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4900_, 0, v___x_4875_);
lean_closure_set(v___f_4900_, 1, v___x_4876_);
lean_closure_set(v___f_4900_, 2, v___x_4877_);
lean_closure_set(v___f_4900_, 3, v___x_4883_);
lean_closure_set(v___f_4900_, 4, v_decls_4887_);
lean_closure_set(v___f_4900_, 5, v_a_4898_);
lean_closure_set(v___f_4900_, 6, v___x_4899_);
v___x_4901_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4902_ = lean_array_to_list(v_a_4895_);
v___x_4903_ = lean_box(0);
v___x_4904_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4902_, v___x_4903_);
v___x_4905_ = l_Lean_MessageData_ofList(v___x_4904_);
v___x_4906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4901_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4907_, 0, v_a_4893_);
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4906_, v___x_4907_, v___f_4900_, v___x_4908_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
return v___x_4909_;
}
else
{
lean_dec(v_a_4895_);
lean_dec(v_a_4893_);
lean_dec(v_decls_4887_);
return v___x_4897_;
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec(v_a_4893_);
lean_dec(v_decls_4887_);
v_a_4910_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4894_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4894_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_decls_4887_);
v_a_4918_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4892_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4892_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4926_, lean_object* v_dec_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4926_, v_dec_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec_ref(v_a_4928_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4944_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4945_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4946_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4947_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4948_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4944_, v___x_4945_, v___x_4946_, v___x_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4964_, lean_object* v_dec_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; uint8_t v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5007_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4964_);
v___x_5008_ = l_Lean_Syntax_isOfKind(v_stx_4964_, v___x_5007_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref(v_dec_4965_);
lean_dec(v_stx_4964_);
v___x_5009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5009_;
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5010_ = lean_unsigned_to_nat(0u);
v___x_5011_ = l_Lean_Syntax_getArg(v_stx_4964_, v___x_5010_);
lean_dec(v_stx_4964_);
v___x_5012_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5011_);
v___x_5013_ = l_Lean_Syntax_isOfKind(v___x_5011_, v___x_5012_);
if (v___x_5013_ == 0)
{
if (v___x_5013_ == 0)
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5025_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5011_);
v___x_5026_ = l_Lean_Syntax_isOfKind(v___x_5011_, v___x_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5027_;
}
else
{
goto v___jp_5014_;
}
}
else
{
goto v___jp_5014_;
}
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5029_; uint8_t v___x_5030_; 
v___x_5028_ = l_Lean_Syntax_getArg(v___x_5011_, v___x_5010_);
v___x_5029_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5028_);
v___x_5030_ = l_Lean_Syntax_isOfKind(v___x_5028_, v___x_5029_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; 
lean_dec(v___x_5028_);
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5031_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5031_;
}
else
{
lean_object* v___x_5032_; lean_object* v_xType_x3f_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5032_ = l_Lean_Syntax_getArg(v___x_5028_, v___x_5010_);
lean_dec(v___x_5028_);
v___x_5061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5032_);
v___x_5062_ = l_Lean_Syntax_isOfKind(v___x_5032_, v___x_5061_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; 
lean_dec(v___x_5032_);
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5063_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5063_;
}
else
{
lean_object* v___x_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5064_ = lean_unsigned_to_nat(1u);
v___x_5065_ = l_Lean_Syntax_getArg(v___x_5011_, v___x_5064_);
v___x_5066_ = l_Lean_Syntax_matchesNull(v___x_5065_, v___x_5010_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
lean_dec(v___x_5032_);
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5067_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v___x_5068_ = lean_unsigned_to_nat(2u);
v___x_5069_ = l_Lean_Syntax_getArg(v___x_5011_, v___x_5068_);
v___x_5070_ = l_Lean_Syntax_isNone(v___x_5069_);
if (v___x_5070_ == 0)
{
uint8_t v___x_5071_; 
lean_inc(v___x_5069_);
v___x_5071_ = l_Lean_Syntax_matchesNull(v___x_5069_, v___x_5064_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; 
lean_dec(v___x_5069_);
lean_dec(v___x_5032_);
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5072_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5072_;
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v___x_5073_ = l_Lean_Syntax_getArg(v___x_5069_, v___x_5010_);
lean_dec(v___x_5069_);
v___x_5074_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5073_);
v___x_5075_ = l_Lean_Syntax_isOfKind(v___x_5073_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; 
lean_dec(v___x_5073_);
lean_dec(v___x_5032_);
lean_dec(v___x_5011_);
lean_dec_ref(v_dec_4965_);
v___x_5076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5076_;
}
else
{
lean_object* v_xType_x3f_5077_; lean_object* v___x_5078_; 
v_xType_x3f_5077_ = l_Lean_Syntax_getArg(v___x_5073_, v___x_5064_);
lean_dec(v___x_5073_);
v___x_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5078_, 0, v_xType_x3f_5077_);
v_xType_x3f_5034_ = v___x_5078_;
v___y_5035_ = v_a_4966_;
v___y_5036_ = v_a_4967_;
v___y_5037_ = v_a_4968_;
v___y_5038_ = v_a_4969_;
v___y_5039_ = v_a_4970_;
v___y_5040_ = v_a_4971_;
v___y_5041_ = v_a_4972_;
goto v___jp_5033_;
}
}
}
else
{
lean_object* v___x_5079_; 
lean_dec(v___x_5069_);
v___x_5079_ = lean_box(0);
v_xType_x3f_5034_ = v___x_5079_;
v___y_5035_ = v_a_4966_;
v___y_5036_ = v_a_4967_;
v___y_5037_ = v_a_4968_;
v___y_5038_ = v_a_4969_;
v___y_5039_ = v_a_4970_;
v___y_5040_ = v_a_4971_;
v___y_5041_ = v_a_4972_;
goto v___jp_5033_;
}
}
}
v___jp_5033_:
{
lean_object* v_ref_5042_; lean_object* v___x_5043_; lean_object* v_tk_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_ref_5042_ = lean_ctor_get(v___y_5040_, 4);
v___x_5043_ = lean_unsigned_to_nat(3u);
v_tk_5044_ = l_Lean_Syntax_getArg(v___x_5011_, v___x_5043_);
v___x_5045_ = lean_unsigned_to_nat(4u);
v___x_5046_ = l_Lean_Syntax_getArg(v___x_5011_, v___x_5045_);
lean_dec(v___x_5011_);
v___x_5047_ = 0;
v___x_5048_ = l_Lean_SourceInfo_fromRef(v_ref_5042_, v___x_5047_);
v___x_5049_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5048_, 2);
v___x_5050_ = l_Lean_Syntax_node1(v___x_5048_, v___x_5029_, v___x_5032_);
v___x_5051_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5052_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5048_);
lean_ctor_set(v___x_5053_, 1, v___x_5051_);
lean_ctor_set(v___x_5053_, 2, v___x_5052_);
if (lean_obj_tag(v_xType_x3f_5034_) == 1)
{
lean_object* v_val_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_val_5054_ = lean_ctor_get(v_xType_x3f_5034_, 0);
lean_inc(v_val_5054_);
lean_dec_ref_known(v_xType_x3f_5034_, 1);
v___x_5055_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5056_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5048_, 2);
v___x_5057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5048_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = l_Lean_Syntax_node2(v___x_5048_, v___x_5055_, v___x_5057_, v_val_5054_);
v___x_5059_ = l_Array_mkArray1___redArg(v___x_5058_);
v___y_4975_ = v___x_5050_;
v___y_4976_ = v___x_5051_;
v___y_4977_ = v___y_5040_;
v___y_4978_ = v___y_5039_;
v___y_4979_ = v___y_5035_;
v___y_4980_ = v___y_5037_;
v___y_4981_ = v___x_5053_;
v___y_4982_ = v___x_5047_;
v___y_4983_ = v___x_5049_;
v___y_4984_ = v___y_5036_;
v___y_4985_ = v___x_5052_;
v___y_4986_ = v___x_5048_;
v___y_4987_ = v___y_5038_;
v___y_4988_ = v___x_5046_;
v___y_4989_ = v___y_5041_;
v___y_4990_ = v_tk_5044_;
v___y_4991_ = v___x_5059_;
goto v___jp_4974_;
}
else
{
lean_object* v___x_5060_; 
lean_dec(v_xType_x3f_5034_);
v___x_5060_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4975_ = v___x_5050_;
v___y_4976_ = v___x_5051_;
v___y_4977_ = v___y_5040_;
v___y_4978_ = v___y_5039_;
v___y_4979_ = v___y_5035_;
v___y_4980_ = v___y_5037_;
v___y_4981_ = v___x_5053_;
v___y_4982_ = v___x_5047_;
v___y_4983_ = v___x_5049_;
v___y_4984_ = v___y_5036_;
v___y_4985_ = v___x_5052_;
v___y_4986_ = v___x_5048_;
v___y_4987_ = v___y_5038_;
v___y_4988_ = v___x_5046_;
v___y_4989_ = v___y_5041_;
v___y_4990_ = v_tk_5044_;
v___y_4991_ = v___x_5060_;
goto v___jp_4974_;
}
}
}
}
v___jp_5014_:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v_decl_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5015_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5016_ = lean_unsigned_to_nat(1u);
v___x_5017_ = lean_mk_empty_array_with_capacity(v___x_5016_);
v___x_5018_ = lean_array_push(v___x_5017_, v___x_5011_);
v___x_5019_ = lean_box(2);
v_decl_5020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5020_, 0, v___x_5019_);
lean_ctor_set(v_decl_5020_, 1, v___x_5015_);
lean_ctor_set(v_decl_5020_, 2, v___x_5018_);
v___x_5021_ = lean_box(0);
v___x_5022_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set_uint8(v___x_5022_, sizeof(void*)*1, v___x_5013_);
lean_ctor_set_uint8(v___x_5022_, sizeof(void*)*1 + 1, v___x_5013_);
lean_ctor_set_uint8(v___x_5022_, sizeof(void*)*1 + 2, v___x_5013_);
lean_ctor_set_uint8(v___x_5022_, sizeof(void*)*1 + 3, v___x_5013_);
lean_ctor_set_uint8(v___x_5022_, sizeof(void*)*1 + 4, v___x_5013_);
v___x_5023_ = lean_box(2);
lean_inc_ref(v_decl_5020_);
v___x_5024_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5022_, v___x_5023_, v_decl_5020_, v_decl_5020_, v_dec_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_5024_;
}
}
v___jp_4974_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_inc_ref(v___y_4985_);
v___x_4992_ = l_Array_append___redArg(v___y_4985_, v___y_4991_);
lean_dec_ref(v___y_4991_);
lean_inc(v___y_4976_);
lean_inc_n(v___y_4986_, 2);
v___x_4993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4993_, 0, v___y_4986_);
lean_ctor_set(v___x_4993_, 1, v___y_4976_);
lean_ctor_set(v___x_4993_, 2, v___x_4992_);
v___x_4994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___y_4986_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
lean_inc(v___y_4983_);
v___x_4996_ = l_Lean_Syntax_node5(v___y_4986_, v___y_4983_, v___y_4975_, v___y_4981_, v___x_4993_, v___x_4995_, v___y_4988_);
v___x_4997_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4998_ = lean_unsigned_to_nat(1u);
v___x_4999_ = lean_mk_empty_array_with_capacity(v___x_4998_);
v___x_5000_ = lean_array_push(v___x_4999_, v___x_4996_);
v___x_5001_ = lean_box(2);
v___x_5002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
lean_ctor_set(v___x_5002_, 1, v___x_4997_);
lean_ctor_set(v___x_5002_, 2, v___x_5000_);
v___x_5003_ = lean_box(0);
v___x_5004_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
lean_ctor_set_uint8(v___x_5004_, sizeof(void*)*1, v___y_4982_);
lean_ctor_set_uint8(v___x_5004_, sizeof(void*)*1 + 1, v___y_4982_);
lean_ctor_set_uint8(v___x_5004_, sizeof(void*)*1 + 2, v___y_4982_);
lean_ctor_set_uint8(v___x_5004_, sizeof(void*)*1 + 3, v___y_4982_);
lean_ctor_set_uint8(v___x_5004_, sizeof(void*)*1 + 4, v___y_4982_);
v___x_5005_ = lean_box(2);
v___x_5006_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5004_, v___x_5005_, v___x_5002_, v___y_4990_, v_dec_4965_, v___y_4979_, v___y_4984_, v___y_4980_, v___y_4987_, v___y_4978_, v___y_4977_, v___y_4989_);
return v___x_5006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5080_, lean_object* v_dec_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5080_, v_dec_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_);
lean_dec(v_a_5088_);
lean_dec_ref(v_a_5087_);
lean_dec(v_a_5086_);
lean_dec_ref(v_a_5085_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec_ref(v_a_5082_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5098_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5099_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5100_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5101_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5102_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5098_, v___x_5099_, v___x_5100_, v___x_5101_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
uint8_t v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5114_ = 0;
v___x_5115_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5105_, v___x_5114_);
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v_____do__lift_5117_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5146_, size_t v_sz_5147_, size_t v_i_5148_, lean_object* v_b_5149_, lean_object* v___y_5150_){
_start:
{
uint8_t v___x_5152_; 
v___x_5152_ = lean_usize_dec_lt(v_i_5148_, v_sz_5147_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; 
v___x_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5153_, 0, v_b_5149_);
return v___x_5153_;
}
else
{
lean_object* v_ref_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v_a_5157_; uint8_t v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; size_t v___x_5191_; size_t v___x_5192_; 
v_ref_5154_ = lean_ctor_get(v___y_5150_, 4);
v___x_5155_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5157_ = lean_array_uget_borrowed(v_as_5146_, v_i_5148_);
v___x_5158_ = 0;
v___x_5159_ = l_Lean_SourceInfo_fromRef(v_ref_5154_, v___x_5158_);
v___x_5160_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5162_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5163_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5159_, 17);
v___x_5164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5159_);
lean_ctor_set(v___x_5164_, 1, v___x_5163_);
v___x_5165_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5159_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5160_, v___x_5166_);
v___x_5168_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5159_);
lean_ctor_set(v___x_5169_, 1, v___x_5160_);
lean_ctor_set(v___x_5169_, 2, v___x_5168_);
lean_inc_ref_n(v___x_5169_, 3);
v___x_5170_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5155_, v___x_5169_);
v___x_5171_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5172_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5173_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5157_, 2);
v___x_5174_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5173_, v_a_5157_);
v___x_5175_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5159_);
lean_ctor_set(v___x_5176_, 1, v___x_5175_);
v___x_5177_ = l_Lean_Syntax_node5(v___x_5159_, v___x_5172_, v___x_5174_, v___x_5169_, v___x_5169_, v___x_5176_, v_a_5157_);
v___x_5178_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5171_, v___x_5177_);
v___x_5179_ = l_Lean_Syntax_node4(v___x_5159_, v___x_5162_, v___x_5164_, v___x_5167_, v___x_5170_, v___x_5178_);
v___x_5180_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5159_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5160_, v___x_5181_);
v___x_5183_ = l_Lean_Syntax_node2(v___x_5159_, v___x_5161_, v___x_5179_, v___x_5182_);
v___x_5184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5159_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = l_Lean_Syntax_node2(v___x_5159_, v___x_5184_, v___x_5186_, v_b_5149_);
v___x_5188_ = l_Lean_Syntax_node2(v___x_5159_, v___x_5161_, v___x_5187_, v___x_5169_);
v___x_5189_ = l_Lean_Syntax_node2(v___x_5159_, v___x_5160_, v___x_5183_, v___x_5188_);
v___x_5190_ = l_Lean_Syntax_node1(v___x_5159_, v___x_5156_, v___x_5189_);
v___x_5191_ = ((size_t)1ULL);
v___x_5192_ = lean_usize_add(v_i_5148_, v___x_5191_);
v_i_5148_ = v___x_5192_;
v_b_5149_ = v___x_5190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5194_, lean_object* v_sz_5195_, lean_object* v_i_5196_, lean_object* v_b_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_){
_start:
{
size_t v_sz_boxed_5200_; size_t v_i_boxed_5201_; lean_object* v_res_5202_; 
v_sz_boxed_5200_ = lean_unbox_usize(v_sz_5195_);
lean_dec(v_sz_5195_);
v_i_boxed_5201_ = lean_unbox_usize(v_i_5196_);
lean_dec(v_i_5196_);
v_res_5202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5194_, v_sz_boxed_5200_, v_i_boxed_5201_, v_b_5197_, v___y_5198_);
lean_dec_ref(v___y_5198_);
lean_dec_ref(v_as_5194_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5203_, size_t v_sz_5204_, size_t v_i_5205_, lean_object* v_b_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
uint8_t v___x_5215_; 
v___x_5215_ = lean_usize_dec_lt(v_i_5205_, v_sz_5204_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5216_; 
v___x_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5216_, 0, v_b_5206_);
return v___x_5216_;
}
else
{
lean_object* v_ref_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v_a_5220_; uint8_t v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; size_t v___x_5254_; size_t v___x_5255_; lean_object* v___x_5256_; 
v_ref_5217_ = lean_ctor_get(v___y_5212_, 4);
v___x_5218_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5220_ = lean_array_uget_borrowed(v_as_5203_, v_i_5205_);
v___x_5221_ = 0;
v___x_5222_ = l_Lean_SourceInfo_fromRef(v_ref_5217_, v___x_5221_);
v___x_5223_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5225_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5226_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5222_, 17);
v___x_5227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5222_);
lean_ctor_set(v___x_5227_, 1, v___x_5226_);
v___x_5228_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5222_);
lean_ctor_set(v___x_5229_, 1, v___x_5228_);
v___x_5230_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5223_, v___x_5229_);
v___x_5231_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5222_);
lean_ctor_set(v___x_5232_, 1, v___x_5223_);
lean_ctor_set(v___x_5232_, 2, v___x_5231_);
lean_inc_ref_n(v___x_5232_, 3);
v___x_5233_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5218_, v___x_5232_);
v___x_5234_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5235_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5236_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5220_, 2);
v___x_5237_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5236_, v_a_5220_);
v___x_5238_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5222_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = l_Lean_Syntax_node5(v___x_5222_, v___x_5235_, v___x_5237_, v___x_5232_, v___x_5232_, v___x_5239_, v_a_5220_);
v___x_5241_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5234_, v___x_5240_);
v___x_5242_ = l_Lean_Syntax_node4(v___x_5222_, v___x_5225_, v___x_5227_, v___x_5230_, v___x_5233_, v___x_5241_);
v___x_5243_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5222_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5223_, v___x_5244_);
v___x_5246_ = l_Lean_Syntax_node2(v___x_5222_, v___x_5224_, v___x_5242_, v___x_5245_);
v___x_5247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5249_, 0, v___x_5222_);
lean_ctor_set(v___x_5249_, 1, v___x_5248_);
v___x_5250_ = l_Lean_Syntax_node2(v___x_5222_, v___x_5247_, v___x_5249_, v_b_5206_);
v___x_5251_ = l_Lean_Syntax_node2(v___x_5222_, v___x_5224_, v___x_5250_, v___x_5232_);
v___x_5252_ = l_Lean_Syntax_node2(v___x_5222_, v___x_5223_, v___x_5246_, v___x_5251_);
v___x_5253_ = l_Lean_Syntax_node1(v___x_5222_, v___x_5219_, v___x_5252_);
v___x_5254_ = ((size_t)1ULL);
v___x_5255_ = lean_usize_add(v_i_5205_, v___x_5254_);
v___x_5256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5203_, v_sz_5204_, v___x_5255_, v___x_5253_, v___y_5212_);
return v___x_5256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5257_, lean_object* v_sz_5258_, lean_object* v_i_5259_, lean_object* v_b_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
size_t v_sz_boxed_5269_; size_t v_i_boxed_5270_; lean_object* v_res_5271_; 
v_sz_boxed_5269_ = lean_unbox_usize(v_sz_5258_);
lean_dec(v_sz_5258_);
v_i_boxed_5270_ = lean_unbox_usize(v_i_5259_);
lean_dec(v_i_5259_);
v_res_5271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5257_, v_sz_boxed_5269_, v_i_boxed_5270_, v_b_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v___y_5261_);
lean_dec_ref(v_as_5257_);
return v_res_5271_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5311_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5312_ = l_String_toRawSubstring_x27(v___x_5311_);
return v___x_5312_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5327_ = l_String_toRawSubstring_x27(v___x_5326_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5344_, lean_object* v_dec_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v___x_5354_; uint8_t v___x_5355_; 
v___x_5354_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5344_);
v___x_5355_ = l_Lean_Syntax_isOfKind(v_stx_5344_, v___x_5354_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; 
lean_dec_ref(v_dec_5345_);
lean_dec(v_stx_5344_);
v___x_5356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5356_;
}
else
{
lean_object* v___y_5358_; lean_object* v___y_5359_; lean_object* v___y_5360_; lean_object* v___y_5361_; uint8_t v___y_5362_; lean_object* v_body_5363_; lean_object* v___y_5364_; lean_object* v___y_5365_; lean_object* v___y_5366_; lean_object* v___y_5367_; lean_object* v___y_5368_; lean_object* v___y_5369_; lean_object* v___y_5370_; lean_object* v___y_5444_; lean_object* v___y_5445_; lean_object* v___y_5446_; lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; uint8_t v___y_5457_; lean_object* v_a_5458_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5474_; lean_object* v___y_5475_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v_mutTk_x3f_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___x_5588_; lean_object* v___x_5589_; uint8_t v___x_5590_; 
v___x_5588_ = lean_unsigned_to_nat(1u);
v___x_5589_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5588_);
v___x_5590_ = l_Lean_Syntax_isNone(v___x_5589_);
if (v___x_5590_ == 0)
{
uint8_t v___x_5591_; 
lean_inc(v___x_5589_);
v___x_5591_ = l_Lean_Syntax_matchesNull(v___x_5589_, v___x_5588_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5592_; 
lean_dec(v___x_5589_);
lean_dec_ref(v_dec_5345_);
lean_dec(v_stx_5344_);
v___x_5592_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5592_;
}
else
{
lean_object* v___x_5593_; lean_object* v_mutTk_x3f_5594_; lean_object* v___x_5595_; 
v___x_5593_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5594_ = l_Lean_Syntax_getArg(v___x_5589_, v___x_5593_);
lean_dec(v___x_5589_);
v___x_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5595_, 0, v_mutTk_x3f_5594_);
v_mutTk_x3f_5557_ = v___x_5595_;
v___y_5558_ = v_a_5346_;
v___y_5559_ = v_a_5347_;
v___y_5560_ = v_a_5348_;
v___y_5561_ = v_a_5349_;
v___y_5562_ = v_a_5350_;
v___y_5563_ = v_a_5351_;
v___y_5564_ = v_a_5352_;
goto v___jp_5556_;
}
}
else
{
lean_object* v___x_5596_; 
lean_dec(v___x_5589_);
v___x_5596_ = lean_box(0);
v_mutTk_x3f_5557_ = v___x_5596_;
v___y_5558_ = v_a_5346_;
v___y_5559_ = v_a_5347_;
v___y_5560_ = v_a_5348_;
v___y_5561_ = v_a_5349_;
v___y_5562_ = v_a_5350_;
v___y_5563_ = v_a_5351_;
v___y_5564_ = v_a_5352_;
goto v___jp_5556_;
}
v___jp_5357_:
{
lean_object* v_eq_x3f_5371_; 
v_eq_x3f_5371_ = lean_ctor_get(v___y_5359_, 0);
lean_inc(v_eq_x3f_5371_);
lean_dec_ref(v___y_5359_);
if (lean_obj_tag(v_eq_x3f_5371_) == 1)
{
lean_object* v_val_5372_; lean_object* v_ref_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v_val_5372_ = lean_ctor_get(v_eq_x3f_5371_, 0);
lean_inc(v_val_5372_);
lean_dec_ref_known(v_eq_x3f_5371_, 1);
v_ref_5373_ = lean_ctor_get(v___y_5369_, 4);
v___x_5374_ = l_Lean_SourceInfo_fromRef(v_ref_5373_, v___y_5362_);
v___x_5375_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5376_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5374_, 19);
v___x_5377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5377_, 0, v___x_5374_);
lean_ctor_set(v___x_5377_, 1, v___x_5376_);
v___x_5378_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5379_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5374_);
lean_ctor_set(v___x_5380_, 1, v___x_5378_);
lean_ctor_set(v___x_5380_, 2, v___x_5379_);
v___x_5381_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5382_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5374_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5378_, v_val_5372_, v___x_5383_);
v___x_5385_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5381_, v___x_5384_, v___y_5358_);
v___x_5386_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5378_, v___x_5385_);
v___x_5387_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5374_);
lean_ctor_set(v___x_5388_, 1, v___x_5387_);
v___x_5389_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5391_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5374_);
lean_ctor_set(v___x_5392_, 1, v___x_5391_);
v___x_5393_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5378_, v___y_5360_);
v___x_5394_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5378_, v___x_5393_);
v___x_5395_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5374_);
lean_ctor_set(v___x_5396_, 1, v___x_5395_);
lean_inc_ref(v___x_5396_);
lean_inc_ref(v___x_5392_);
v___x_5397_ = l_Lean_Syntax_node4(v___x_5374_, v___x_5390_, v___x_5392_, v___x_5394_, v___x_5396_, v_body_5363_);
v___x_5398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5399_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5374_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
v___x_5401_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5398_, v___x_5400_);
v___x_5402_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5378_, v___x_5401_);
v___x_5403_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5378_, v___x_5402_);
v___x_5404_ = l_Lean_Syntax_node4(v___x_5374_, v___x_5390_, v___x_5392_, v___x_5403_, v___x_5396_, v___y_5361_);
v___x_5405_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5378_, v___x_5397_, v___x_5404_);
v___x_5406_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5389_, v___x_5405_);
lean_inc_ref_n(v___x_5380_, 2);
v___x_5407_ = l_Lean_Syntax_node7(v___x_5374_, v___x_5375_, v___x_5377_, v___x_5380_, v___x_5380_, v___x_5380_, v___x_5386_, v___x_5388_, v___x_5406_);
v___x_5408_ = l_Lean_Elab_Do_elabDoElem(v___x_5407_, v_dec_5345_, v___x_5355_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
return v___x_5408_;
}
else
{
lean_object* v_ref_5409_; lean_object* v___x_5410_; lean_object* v_a_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec(v_eq_x3f_5371_);
v_ref_5409_ = lean_ctor_get(v___y_5369_, 4);
v___x_5410_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5409_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
lean_inc_n(v_a_5411_, 18);
lean_dec_ref(v___x_5410_);
v___x_5412_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5413_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5414_, 0, v_a_5411_);
lean_ctor_set(v___x_5414_, 1, v___x_5413_);
v___x_5415_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5416_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5417_, 0, v_a_5411_);
lean_ctor_set(v___x_5417_, 1, v___x_5415_);
lean_ctor_set(v___x_5417_, 2, v___x_5416_);
v___x_5418_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5417_, 3);
v___x_5419_ = l_Lean_Syntax_node2(v_a_5411_, v___x_5418_, v___x_5417_, v___y_5358_);
v___x_5420_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5415_, v___x_5419_);
v___x_5421_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5422_, 0, v_a_5411_);
lean_ctor_set(v___x_5422_, 1, v___x_5421_);
v___x_5423_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5425_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5426_, 0, v_a_5411_);
lean_ctor_set(v___x_5426_, 1, v___x_5425_);
v___x_5427_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5415_, v___y_5360_);
v___x_5428_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5415_, v___x_5427_);
v___x_5429_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5430_, 0, v_a_5411_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
lean_inc_ref(v___x_5430_);
lean_inc_ref(v___x_5426_);
v___x_5431_ = l_Lean_Syntax_node4(v_a_5411_, v___x_5424_, v___x_5426_, v___x_5428_, v___x_5430_, v_body_5363_);
v___x_5432_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5433_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5434_, 0, v_a_5411_);
lean_ctor_set(v___x_5434_, 1, v___x_5433_);
v___x_5435_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5432_, v___x_5434_);
v___x_5436_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5415_, v___x_5435_);
v___x_5437_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5415_, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_node4(v_a_5411_, v___x_5424_, v___x_5426_, v___x_5437_, v___x_5430_, v___y_5361_);
v___x_5439_ = l_Lean_Syntax_node2(v_a_5411_, v___x_5415_, v___x_5431_, v___x_5438_);
v___x_5440_ = l_Lean_Syntax_node1(v_a_5411_, v___x_5423_, v___x_5439_);
v___x_5441_ = l_Lean_Syntax_node7(v_a_5411_, v___x_5412_, v___x_5414_, v___x_5417_, v___x_5417_, v___x_5417_, v___x_5420_, v___x_5422_, v___x_5440_);
v___x_5442_ = l_Lean_Elab_Do_elabDoElem(v___x_5441_, v_dec_5345_, v___x_5355_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
return v___x_5442_;
}
}
v___jp_5443_:
{
if (lean_obj_tag(v___y_5452_) == 0)
{
lean_dec_ref(v___y_5454_);
v___y_5358_ = v___y_5444_;
v___y_5359_ = v___y_5445_;
v___y_5360_ = v___y_5449_;
v___y_5361_ = v___y_5451_;
v___y_5362_ = v___y_5457_;
v_body_5363_ = v_a_5458_;
v___y_5364_ = v___y_5448_;
v___y_5365_ = v___y_5450_;
v___y_5366_ = v___y_5453_;
v___y_5367_ = v___y_5455_;
v___y_5368_ = v___y_5446_;
v___y_5369_ = v___y_5456_;
v___y_5370_ = v___y_5447_;
goto v___jp_5357_;
}
else
{
lean_dec_ref_known(v___y_5452_, 1);
if (v___x_5355_ == 0)
{
lean_dec_ref(v___y_5454_);
v___y_5358_ = v___y_5444_;
v___y_5359_ = v___y_5445_;
v___y_5360_ = v___y_5449_;
v___y_5361_ = v___y_5451_;
v___y_5362_ = v___y_5457_;
v_body_5363_ = v_a_5458_;
v___y_5364_ = v___y_5448_;
v___y_5365_ = v___y_5450_;
v___y_5366_ = v___y_5453_;
v___y_5367_ = v___y_5455_;
v___y_5368_ = v___y_5446_;
v___y_5369_ = v___y_5456_;
v___y_5370_ = v___y_5447_;
goto v___jp_5357_;
}
else
{
size_t v_sz_5459_; size_t v___x_5460_; lean_object* v___x_5461_; 
v_sz_5459_ = lean_array_size(v___y_5454_);
v___x_5460_ = ((size_t)0ULL);
v___x_5461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5454_, v_sz_5459_, v___x_5460_, v_a_5458_, v___y_5448_, v___y_5450_, v___y_5453_, v___y_5455_, v___y_5446_, v___y_5456_, v___y_5447_);
lean_dec_ref(v___y_5454_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
lean_inc(v_a_5462_);
lean_dec_ref_known(v___x_5461_, 1);
v___y_5358_ = v___y_5444_;
v___y_5359_ = v___y_5445_;
v___y_5360_ = v___y_5449_;
v___y_5361_ = v___y_5451_;
v___y_5362_ = v___y_5457_;
v_body_5363_ = v_a_5462_;
v___y_5364_ = v___y_5448_;
v___y_5365_ = v___y_5450_;
v___y_5366_ = v___y_5453_;
v___y_5367_ = v___y_5455_;
v___y_5368_ = v___y_5446_;
v___y_5369_ = v___y_5456_;
v___y_5370_ = v___y_5447_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_dec(v___y_5451_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v_dec_5345_);
v_a_5463_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5461_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5461_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
}
v___jp_5471_:
{
uint8_t v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5485_ = 0;
v___x_5486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5487_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5479_, v___y_5480_, v___x_5486_, v___y_5477_, v___y_5481_, v___y_5482_, v___y_5473_, v___y_5483_, v___y_5474_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v___x_5489_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref_known(v___x_5487_, 1);
v___x_5489_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5488_, v___y_5476_, v___y_5477_, v___y_5481_, v___y_5482_, v___y_5473_, v___y_5483_, v___y_5474_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v___x_5490_; 
lean_dec_ref_known(v___x_5489_, 1);
lean_inc(v___y_5475_);
v___x_5490_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5475_, v___y_5477_, v___y_5481_, v___y_5482_, v___y_5473_, v___y_5483_, v___y_5474_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
lean_inc(v___y_5480_);
v___x_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___y_5480_);
v___x_5493_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5492_, v_a_5491_, v___y_5476_, v___y_5477_, v___y_5481_, v___y_5482_, v___y_5473_, v___y_5483_, v___y_5474_);
lean_dec_ref_known(v___x_5492_, 1);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_dec_ref_known(v___x_5493_, 1);
if (lean_obj_tag(v___y_5484_) == 0)
{
lean_object* v_toCold_5494_; lean_object* v_ref_5495_; lean_object* v_currMacroScope_5496_; lean_object* v___x_5497_; lean_object* v_a_5498_; lean_object* v_quotContext_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; 
v_toCold_5494_ = lean_ctor_get(v___y_5483_, 0);
v_ref_5495_ = lean_ctor_get(v___y_5483_, 4);
v_currMacroScope_5496_ = lean_ctor_get(v___y_5483_, 9);
v___x_5497_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5495_, v___y_5476_, v___y_5477_, v___y_5481_, v___y_5482_, v___y_5473_, v___y_5483_, v___y_5474_);
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc_n(v_a_5498_, 9);
lean_dec_ref(v___x_5497_);
v_quotContext_5499_ = lean_ctor_get(v_toCold_5494_, 2);
v___x_5500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5501_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5503_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5504_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5505_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5506_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5496_, 2);
lean_inc_n(v_quotContext_5499_, 2);
v___x_5507_ = l_Lean_addMacroScope(v_quotContext_5499_, v___x_5506_, v_currMacroScope_5496_);
v___x_5508_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5509_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5509_, 0, v_a_5498_);
lean_ctor_set(v___x_5509_, 1, v___x_5505_);
lean_ctor_set(v___x_5509_, 2, v___x_5507_);
lean_ctor_set(v___x_5509_, 3, v___x_5508_);
v___x_5510_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5511_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5512_ = l_Lean_addMacroScope(v_quotContext_5499_, v___x_5511_, v_currMacroScope_5496_);
v___x_5513_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5514_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5514_, 0, v_a_5498_);
lean_ctor_set(v___x_5514_, 1, v___x_5510_);
lean_ctor_set(v___x_5514_, 2, v___x_5512_);
lean_ctor_set(v___x_5514_, 3, v___x_5513_);
v___x_5515_ = l_Lean_Syntax_node1(v_a_5498_, v___x_5501_, v___x_5514_);
v___x_5516_ = l_Lean_Syntax_node2(v_a_5498_, v___x_5504_, v___x_5509_, v___x_5515_);
v___x_5517_ = l_Lean_Syntax_node1(v_a_5498_, v___x_5503_, v___x_5516_);
v___x_5518_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5519_, 0, v_a_5498_);
lean_ctor_set(v___x_5519_, 1, v___x_5501_);
lean_ctor_set(v___x_5519_, 2, v___x_5518_);
v___x_5520_ = l_Lean_Syntax_node2(v_a_5498_, v___x_5502_, v___x_5517_, v___x_5519_);
v___x_5521_ = l_Lean_Syntax_node1(v_a_5498_, v___x_5501_, v___x_5520_);
v___x_5522_ = l_Lean_Syntax_node1(v_a_5498_, v___x_5500_, v___x_5521_);
v___y_5444_ = v___y_5472_;
v___y_5445_ = v_a_5488_;
v___y_5446_ = v___y_5473_;
v___y_5447_ = v___y_5474_;
v___y_5448_ = v___y_5476_;
v___y_5449_ = v___y_5475_;
v___y_5450_ = v___y_5477_;
v___y_5451_ = v___y_5478_;
v___y_5452_ = v___y_5480_;
v___y_5453_ = v___y_5481_;
v___y_5454_ = v_a_5491_;
v___y_5455_ = v___y_5482_;
v___y_5456_ = v___y_5483_;
v___y_5457_ = v___x_5485_;
v_a_5458_ = v___x_5522_;
goto v___jp_5443_;
}
else
{
lean_object* v_val_5523_; 
v_val_5523_ = lean_ctor_get(v___y_5484_, 0);
lean_inc(v_val_5523_);
lean_dec_ref_known(v___y_5484_, 1);
v___y_5444_ = v___y_5472_;
v___y_5445_ = v_a_5488_;
v___y_5446_ = v___y_5473_;
v___y_5447_ = v___y_5474_;
v___y_5448_ = v___y_5476_;
v___y_5449_ = v___y_5475_;
v___y_5450_ = v___y_5477_;
v___y_5451_ = v___y_5478_;
v___y_5452_ = v___y_5480_;
v___y_5453_ = v___y_5481_;
v___y_5454_ = v_a_5491_;
v___y_5455_ = v___y_5482_;
v___y_5456_ = v___y_5483_;
v___y_5457_ = v___x_5485_;
v_a_5458_ = v_val_5523_;
goto v___jp_5443_;
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec(v_a_5491_);
lean_dec(v_a_5488_);
lean_dec(v___y_5484_);
lean_dec(v___y_5480_);
lean_dec(v___y_5478_);
lean_dec(v___y_5475_);
lean_dec(v___y_5472_);
lean_dec_ref(v_dec_5345_);
v_a_5524_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5493_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5493_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec(v_a_5488_);
lean_dec(v___y_5484_);
lean_dec(v___y_5480_);
lean_dec(v___y_5478_);
lean_dec(v___y_5475_);
lean_dec(v___y_5472_);
lean_dec_ref(v_dec_5345_);
v_a_5532_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5490_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5490_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec(v_a_5488_);
lean_dec(v___y_5484_);
lean_dec(v___y_5480_);
lean_dec(v___y_5478_);
lean_dec(v___y_5475_);
lean_dec(v___y_5472_);
lean_dec_ref(v_dec_5345_);
v_a_5540_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5489_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5489_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
else
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5555_; 
lean_dec(v___y_5484_);
lean_dec(v___y_5480_);
lean_dec(v___y_5478_);
lean_dec(v___y_5475_);
lean_dec(v___y_5472_);
lean_dec_ref(v_dec_5345_);
v_a_5548_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5550_ = v___x_5487_;
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5487_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
}
}
v___jp_5556_:
{
lean_object* v___x_5565_; lean_object* v_cfg_5566_; lean_object* v___x_5567_; uint8_t v___x_5568_; 
v___x_5565_ = lean_unsigned_to_nat(2u);
v_cfg_5566_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5565_);
v___x_5567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5566_);
v___x_5568_ = l_Lean_Syntax_isOfKind(v_cfg_5566_, v___x_5567_);
if (v___x_5568_ == 0)
{
lean_object* v___x_5569_; 
lean_dec(v_cfg_5566_);
lean_dec(v_mutTk_x3f_5557_);
lean_dec_ref(v_dec_5345_);
lean_dec(v_stx_5344_);
v___x_5569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5569_;
}
else
{
lean_object* v___x_5570_; lean_object* v_pattern_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5570_ = lean_unsigned_to_nat(3u);
v_pattern_5571_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5570_);
v___x_5572_ = lean_unsigned_to_nat(5u);
v___x_5573_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5572_);
v___x_5574_ = lean_unsigned_to_nat(7u);
v___x_5575_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5574_);
v___x_5576_ = lean_unsigned_to_nat(8u);
v___x_5577_ = l_Lean_Syntax_getArg(v_stx_5344_, v___x_5576_);
lean_dec(v_stx_5344_);
v___x_5578_ = l_Lean_Syntax_getOptional_x3f(v___x_5577_);
lean_dec(v___x_5577_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v___x_5579_; 
v___x_5579_ = lean_box(0);
v___y_5472_ = v___x_5573_;
v___y_5473_ = v___y_5562_;
v___y_5474_ = v___y_5564_;
v___y_5475_ = v_pattern_5571_;
v___y_5476_ = v___y_5558_;
v___y_5477_ = v___y_5559_;
v___y_5478_ = v___x_5575_;
v___y_5479_ = v_cfg_5566_;
v___y_5480_ = v_mutTk_x3f_5557_;
v___y_5481_ = v___y_5560_;
v___y_5482_ = v___y_5561_;
v___y_5483_ = v___y_5563_;
v___y_5484_ = v___x_5579_;
goto v___jp_5471_;
}
else
{
lean_object* v_val_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5587_; 
v_val_5580_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5582_ = v___x_5578_;
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_val_5580_);
lean_dec(v___x_5578_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5585_; 
if (v_isShared_5583_ == 0)
{
v___x_5585_ = v___x_5582_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_val_5580_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
v___y_5472_ = v___x_5573_;
v___y_5473_ = v___y_5562_;
v___y_5474_ = v___y_5564_;
v___y_5475_ = v_pattern_5571_;
v___y_5476_ = v___y_5558_;
v___y_5477_ = v___y_5559_;
v___y_5478_ = v___x_5575_;
v___y_5479_ = v_cfg_5566_;
v___y_5480_ = v_mutTk_x3f_5557_;
v___y_5481_ = v___y_5560_;
v___y_5482_ = v___y_5561_;
v___y_5483_ = v___y_5563_;
v___y_5484_ = v___x_5585_;
goto v___jp_5471_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5597_, lean_object* v_dec_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5597_, v_dec_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_);
lean_dec(v_a_5605_);
lean_dec_ref(v_a_5604_);
lean_dec(v_a_5603_);
lean_dec_ref(v_a_5602_);
lean_dec(v_a_5601_);
lean_dec_ref(v_a_5600_);
lean_dec_ref(v_a_5599_);
return v_res_5607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5608_, size_t v_sz_5609_, size_t v_i_5610_, lean_object* v_b_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_){
_start:
{
lean_object* v___x_5620_; 
v___x_5620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5608_, v_sz_5609_, v_i_5610_, v_b_5611_, v___y_5617_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5621_, lean_object* v_sz_5622_, lean_object* v_i_5623_, lean_object* v_b_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
size_t v_sz_boxed_5633_; size_t v_i_boxed_5634_; lean_object* v_res_5635_; 
v_sz_boxed_5633_ = lean_unbox_usize(v_sz_5622_);
lean_dec(v_sz_5622_);
v_i_boxed_5634_ = lean_unbox_usize(v_i_5623_);
lean_dec(v_i_5623_);
v_res_5635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5621_, v_sz_boxed_5633_, v_i_boxed_5634_, v_b_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec_ref(v_as_5621_);
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
v___x_5643_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5644_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5645_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5646_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5647_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5643_, v___x_5644_, v___x_5645_, v___x_5646_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5648_){
_start:
{
lean_object* v_res_5649_; 
v_res_5649_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5649_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; 
v___x_5657_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5658_ = l_Lean_stringToMessageData(v___x_5657_);
return v___x_5658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5659_, lean_object* v_dec_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v___x_5669_; uint8_t v___x_5670_; 
v___x_5669_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5659_);
v___x_5670_ = l_Lean_Syntax_isOfKind(v_stx_5659_, v___x_5669_);
if (v___x_5670_ == 0)
{
lean_object* v___x_5671_; 
lean_dec_ref(v_dec_5660_);
lean_dec(v_stx_5659_);
v___x_5671_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5671_;
}
else
{
lean_object* v___x_5672_; lean_object* v_tk_5673_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v___y_5677_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; uint8_t v___y_5719_; lean_object* v___y_5722_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; uint8_t v___y_5733_; lean_object* v_mutTk_x3f_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; lean_object* v___y_5742_; lean_object* v___y_5743_; lean_object* v___x_5773_; lean_object* v___x_5774_; uint8_t v___x_5775_; 
v___x_5672_ = lean_unsigned_to_nat(0u);
v_tk_5673_ = l_Lean_Syntax_getArg(v_stx_5659_, v___x_5672_);
v___x_5773_ = lean_unsigned_to_nat(1u);
v___x_5774_ = l_Lean_Syntax_getArg(v_stx_5659_, v___x_5773_);
v___x_5775_ = l_Lean_Syntax_isNone(v___x_5774_);
if (v___x_5775_ == 0)
{
uint8_t v___x_5776_; 
lean_inc(v___x_5774_);
v___x_5776_ = l_Lean_Syntax_matchesNull(v___x_5774_, v___x_5773_);
if (v___x_5776_ == 0)
{
lean_object* v___x_5777_; 
lean_dec(v___x_5774_);
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
lean_dec(v_stx_5659_);
v___x_5777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5777_;
}
else
{
lean_object* v_mutTk_x3f_5778_; lean_object* v___x_5779_; 
v_mutTk_x3f_5778_ = l_Lean_Syntax_getArg(v___x_5774_, v___x_5672_);
lean_dec(v___x_5774_);
v___x_5779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5779_, 0, v_mutTk_x3f_5778_);
v_mutTk_x3f_5736_ = v___x_5779_;
v___y_5737_ = v_a_5661_;
v___y_5738_ = v_a_5662_;
v___y_5739_ = v_a_5663_;
v___y_5740_ = v_a_5664_;
v___y_5741_ = v_a_5665_;
v___y_5742_ = v_a_5666_;
v___y_5743_ = v_a_5667_;
goto v___jp_5735_;
}
}
else
{
lean_object* v___x_5780_; 
lean_dec(v___x_5774_);
v___x_5780_ = lean_box(0);
v_mutTk_x3f_5736_ = v___x_5780_;
v___y_5737_ = v_a_5661_;
v___y_5738_ = v_a_5662_;
v___y_5739_ = v_a_5663_;
v___y_5740_ = v_a_5664_;
v___y_5741_ = v_a_5665_;
v___y_5742_ = v_a_5666_;
v___y_5743_ = v_a_5667_;
goto v___jp_5735_;
}
v___jp_5674_:
{
lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5684_, 0, v___y_5676_);
v___x_5685_ = l_Lean_Elab_Do_elabDoArrow(v___x_5684_, v___y_5675_, v_tk_5673_, v_dec_5660_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v_tk_5673_);
return v___x_5685_;
}
v___jp_5686_:
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v_a_5699_; lean_object* v___x_5701_; uint8_t v_isShared_5702_; uint8_t v_isSharedCheck_5706_; 
lean_dec(v___y_5693_);
lean_dec(v___y_5689_);
v___x_5697_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5698_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5688_, v___x_5697_, v___y_5687_, v___y_5691_, v___y_5696_, v___y_5692_);
lean_dec(v___y_5688_);
v_a_5699_ = lean_ctor_get(v___x_5698_, 0);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5698_);
if (v_isSharedCheck_5706_ == 0)
{
v___x_5701_ = v___x_5698_;
v_isShared_5702_ = v_isSharedCheck_5706_;
goto v_resetjp_5700_;
}
else
{
lean_inc(v_a_5699_);
lean_dec(v___x_5698_);
v___x_5701_ = lean_box(0);
v_isShared_5702_ = v_isSharedCheck_5706_;
goto v_resetjp_5700_;
}
v_resetjp_5700_:
{
lean_object* v___x_5704_; 
if (v_isShared_5702_ == 0)
{
v___x_5704_ = v___x_5701_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_a_5699_);
v___x_5704_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
return v___x_5704_;
}
}
}
v___jp_5707_:
{
if (v___y_5719_ == 0)
{
lean_object* v_eq_x3f_5720_; 
v_eq_x3f_5720_ = lean_ctor_get(v___y_5710_, 0);
lean_inc(v_eq_x3f_5720_);
lean_dec_ref(v___y_5710_);
if (lean_obj_tag(v_eq_x3f_5720_) == 0)
{
lean_dec(v___y_5708_);
v___y_5675_ = v___y_5711_;
v___y_5676_ = v___y_5715_;
v___y_5677_ = v___y_5717_;
v___y_5678_ = v___y_5716_;
v___y_5679_ = v___y_5712_;
v___y_5680_ = v___y_5709_;
v___y_5681_ = v___y_5713_;
v___y_5682_ = v___y_5718_;
v___y_5683_ = v___y_5714_;
goto v___jp_5674_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5720_, 1);
if (v___x_5670_ == 0)
{
lean_dec(v___y_5708_);
v___y_5675_ = v___y_5711_;
v___y_5676_ = v___y_5715_;
v___y_5677_ = v___y_5717_;
v___y_5678_ = v___y_5716_;
v___y_5679_ = v___y_5712_;
v___y_5680_ = v___y_5709_;
v___y_5681_ = v___y_5713_;
v___y_5682_ = v___y_5718_;
v___y_5683_ = v___y_5714_;
goto v___jp_5674_;
}
else
{
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
v___y_5687_ = v___y_5709_;
v___y_5688_ = v___y_5708_;
v___y_5689_ = v___y_5711_;
v___y_5690_ = v___y_5712_;
v___y_5691_ = v___y_5713_;
v___y_5692_ = v___y_5714_;
v___y_5693_ = v___y_5715_;
v___y_5694_ = v___y_5716_;
v___y_5695_ = v___y_5717_;
v___y_5696_ = v___y_5718_;
goto v___jp_5686_;
}
}
}
else
{
lean_dec_ref(v___y_5710_);
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
v___y_5687_ = v___y_5709_;
v___y_5688_ = v___y_5708_;
v___y_5689_ = v___y_5711_;
v___y_5690_ = v___y_5712_;
v___y_5691_ = v___y_5713_;
v___y_5692_ = v___y_5714_;
v___y_5693_ = v___y_5715_;
v___y_5694_ = v___y_5716_;
v___y_5695_ = v___y_5717_;
v___y_5696_ = v___y_5718_;
goto v___jp_5686_;
}
}
v___jp_5721_:
{
if (v___y_5733_ == 0)
{
uint8_t v_zeta_5734_; 
v_zeta_5734_ = lean_ctor_get_uint8(v___y_5724_, sizeof(void*)*1 + 2);
v___y_5708_ = v___y_5723_;
v___y_5709_ = v___y_5722_;
v___y_5710_ = v___y_5724_;
v___y_5711_ = v___y_5726_;
v___y_5712_ = v___y_5725_;
v___y_5713_ = v___y_5727_;
v___y_5714_ = v___y_5728_;
v___y_5715_ = v___y_5731_;
v___y_5716_ = v___y_5730_;
v___y_5717_ = v___y_5729_;
v___y_5718_ = v___y_5732_;
v___y_5719_ = v_zeta_5734_;
goto v___jp_5707_;
}
else
{
v___y_5708_ = v___y_5723_;
v___y_5709_ = v___y_5722_;
v___y_5710_ = v___y_5724_;
v___y_5711_ = v___y_5726_;
v___y_5712_ = v___y_5725_;
v___y_5713_ = v___y_5727_;
v___y_5714_ = v___y_5728_;
v___y_5715_ = v___y_5731_;
v___y_5716_ = v___y_5730_;
v___y_5717_ = v___y_5729_;
v___y_5718_ = v___y_5732_;
v___y_5719_ = v___x_5670_;
goto v___jp_5707_;
}
}
v___jp_5735_:
{
lean_object* v___x_5744_; lean_object* v_cfg_5745_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5744_ = lean_unsigned_to_nat(2u);
v_cfg_5745_ = l_Lean_Syntax_getArg(v_stx_5659_, v___x_5744_);
v___x_5746_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5745_);
v___x_5747_ = l_Lean_Syntax_isOfKind(v_cfg_5745_, v___x_5746_);
if (v___x_5747_ == 0)
{
lean_object* v___x_5748_; 
lean_dec(v_cfg_5745_);
lean_dec(v_mutTk_x3f_5736_);
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
lean_dec(v_stx_5659_);
v___x_5748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5748_;
}
else
{
lean_object* v___x_5749_; lean_object* v___x_5750_; 
v___x_5749_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5745_);
v___x_5750_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5745_, v_mutTk_x3f_5736_, v___x_5749_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5752_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
lean_inc(v_a_5751_);
lean_dec_ref_known(v___x_5750_, 1);
v___x_5752_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5751_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
if (lean_obj_tag(v___x_5752_) == 0)
{
uint8_t v_nondep_5753_; uint8_t v_usedOnly_5754_; lean_object* v___x_5755_; lean_object* v_decl_5756_; 
lean_dec_ref_known(v___x_5752_, 1);
v_nondep_5753_ = lean_ctor_get_uint8(v_a_5751_, sizeof(void*)*1);
v_usedOnly_5754_ = lean_ctor_get_uint8(v_a_5751_, sizeof(void*)*1 + 1);
v___x_5755_ = lean_unsigned_to_nat(3u);
v_decl_5756_ = l_Lean_Syntax_getArg(v_stx_5659_, v___x_5755_);
lean_dec(v_stx_5659_);
if (v_nondep_5753_ == 0)
{
v___y_5722_ = v___y_5740_;
v___y_5723_ = v_cfg_5745_;
v___y_5724_ = v_a_5751_;
v___y_5725_ = v___y_5739_;
v___y_5726_ = v_decl_5756_;
v___y_5727_ = v___y_5741_;
v___y_5728_ = v___y_5743_;
v___y_5729_ = v___y_5737_;
v___y_5730_ = v___y_5738_;
v___y_5731_ = v_mutTk_x3f_5736_;
v___y_5732_ = v___y_5742_;
v___y_5733_ = v_usedOnly_5754_;
goto v___jp_5721_;
}
else
{
v___y_5722_ = v___y_5740_;
v___y_5723_ = v_cfg_5745_;
v___y_5724_ = v_a_5751_;
v___y_5725_ = v___y_5739_;
v___y_5726_ = v_decl_5756_;
v___y_5727_ = v___y_5741_;
v___y_5728_ = v___y_5743_;
v___y_5729_ = v___y_5737_;
v___y_5730_ = v___y_5738_;
v___y_5731_ = v_mutTk_x3f_5736_;
v___y_5732_ = v___y_5742_;
v___y_5733_ = v___x_5670_;
goto v___jp_5721_;
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec(v_a_5751_);
lean_dec(v_cfg_5745_);
lean_dec(v_mutTk_x3f_5736_);
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
lean_dec(v_stx_5659_);
v_a_5757_ = lean_ctor_get(v___x_5752_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5752_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5752_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5752_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
lean_dec(v_cfg_5745_);
lean_dec(v_mutTk_x3f_5736_);
lean_dec(v_tk_5673_);
lean_dec_ref(v_dec_5660_);
lean_dec(v_stx_5659_);
v_a_5765_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5750_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5750_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5781_, lean_object* v_dec_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5781_, v_dec_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_);
lean_dec(v_a_5789_);
lean_dec_ref(v_a_5788_);
lean_dec(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
lean_dec_ref(v_a_5783_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; 
v___x_5799_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5800_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5801_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5802_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5803_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5799_, v___x_5800_, v___x_5801_, v___x_5802_);
return v___x_5803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5812_, lean_object* v_dec_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_){
_start:
{
lean_object* v___x_5822_; uint8_t v___x_5823_; 
v___x_5822_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5812_);
v___x_5823_ = l_Lean_Syntax_isOfKind(v_stx_5812_, v___x_5822_);
if (v___x_5823_ == 0)
{
lean_object* v___x_5824_; 
lean_dec_ref(v_dec_5813_);
lean_dec(v_stx_5812_);
v___x_5824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5824_;
}
else
{
lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; uint8_t v___x_5828_; 
v___x_5825_ = lean_unsigned_to_nat(0u);
v___x_5826_ = l_Lean_Syntax_getArg(v_stx_5812_, v___x_5825_);
lean_dec(v_stx_5812_);
v___x_5827_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5826_);
v___x_5828_ = l_Lean_Syntax_isOfKind(v___x_5826_, v___x_5827_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; uint8_t v___x_5830_; 
v___x_5829_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5826_);
v___x_5830_ = l_Lean_Syntax_isOfKind(v___x_5826_, v___x_5829_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; 
lean_dec(v___x_5826_);
lean_dec_ref(v_dec_5813_);
v___x_5831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5831_;
}
else
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_box(2);
lean_inc(v___x_5826_);
v___x_5833_ = l_Lean_Elab_Do_elabDoArrow(v___x_5832_, v___x_5826_, v___x_5826_, v_dec_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_);
lean_dec(v___x_5826_);
return v___x_5833_;
}
}
else
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_box(2);
lean_inc(v___x_5826_);
v___x_5835_ = l_Lean_Elab_Do_elabDoArrow(v___x_5834_, v___x_5826_, v___x_5826_, v_dec_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_);
lean_dec(v___x_5826_);
return v___x_5835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5836_, lean_object* v_dec_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
lean_object* v_res_5846_; 
v_res_5846_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5836_, v_dec_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_);
lean_dec(v_a_5844_);
lean_dec_ref(v_a_5843_);
lean_dec(v_a_5842_);
lean_dec_ref(v_a_5841_);
lean_dec(v_a_5840_);
lean_dec_ref(v_a_5839_);
lean_dec_ref(v_a_5838_);
return v_res_5846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5854_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5855_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5856_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5857_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5858_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5854_, v___x_5855_, v___x_5856_, v___x_5857_);
return v___x_5858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5859_){
_start:
{
lean_object* v_res_5860_; 
v_res_5860_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5860_;
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
