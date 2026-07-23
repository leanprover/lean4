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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0;
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
v___x_704_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_693_, v_a_702_, v___x_540_, v___x_540_, v___x_703_, v___y_699_, v___y_695_, v___y_701_, v___y_698_, v___y_700_, v___y_697_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref_known(v___x_704_, 1);
v___x_705_ = l_Lean_TSyntax_getId(v_x_693_);
v___x_706_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_705_, v___y_701_, v___y_698_, v___y_700_, v___y_697_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_LocalDecl_type(v_a_707_);
lean_dec(v_a_707_);
v___x_709_ = l_Lean_Elab_Term_exprToSyntax(v___x_708_, v___y_699_, v___y_695_, v___y_701_, v___y_698_, v___y_700_, v___y_697_);
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
v_ref_714_ = lean_ctor_get(v___y_700_, 5);
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
v___x_728_ = l_Lean_Syntax_node5(v___x_716_, v___x_547_, v___x_717_, v___x_720_, v___x_725_, v___x_727_, v___y_696_);
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
lean_dec(v___y_696_);
lean_dec(v_x_693_);
return v___x_709_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___y_696_);
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
lean_dec(v___y_696_);
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
v___y_696_ = v___x_759_;
v___y_697_ = v___y_757_;
v___y_698_ = v___y_755_;
v___y_699_ = v___y_752_;
v___y_700_ = v___y_756_;
v___y_701_ = v___y_754_;
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
v___y_696_ = v___x_759_;
v___y_697_ = v___y_757_;
v___y_698_ = v___y_755_;
v___y_699_ = v___y_752_;
v___y_700_ = v___y_756_;
v___y_701_ = v___y_754_;
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
uint8_t v___x_98695__boxed_1164_; uint8_t v___x_98698__boxed_1165_; lean_object* v_res_1166_; 
v___x_98695__boxed_1164_ = lean_unbox(v___x_1153_);
v___x_98698__boxed_1165_ = lean_unbox(v___x_1156_);
v_res_1166_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1151_, v___x_1152_, v___x_98695__boxed_1164_, v___x_1154_, v___x_1155_, v___x_98698__boxed_1165_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
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
size_t v_x_98818__boxed_1308_; size_t v_x_98819__boxed_1309_; lean_object* v_res_1310_; 
v_x_98818__boxed_1308_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_x_98819__boxed_1309_ = lean_unbox_usize(v_x_1305_);
lean_dec(v_x_1305_);
v_res_1310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1303_, v_x_98818__boxed_1308_, v_x_98819__boxed_1309_, v_x_1306_, v_x_1307_);
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
uint8_t v___x_99131__boxed_1518_; uint8_t v___x_99132__boxed_1519_; uint8_t v___y_99134__boxed_1520_; lean_object* v_res_1521_; 
v___x_99131__boxed_1518_ = lean_unbox(v___x_1506_);
v___x_99132__boxed_1519_ = lean_unbox(v___x_1507_);
v___y_99134__boxed_1520_ = lean_unbox(v___y_1509_);
v_res_1521_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1504_, v_value_1505_, v___x_99131__boxed_1518_, v___x_99132__boxed_1519_, v___x_1508_, v___y_99134__boxed_1520_, v_xs_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
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
uint8_t v_zeta_boxed_1612_; uint8_t v___y_99358__boxed_1613_; uint8_t v_usedOnly_boxed_1614_; uint8_t v___x_99359__boxed_1615_; uint8_t v___x_99360__boxed_1616_; lean_object* v_res_1617_; 
v_zeta_boxed_1612_ = lean_unbox(v_zeta_1596_);
v___y_99358__boxed_1613_ = lean_unbox(v___y_1597_);
v_usedOnly_boxed_1614_ = lean_unbox(v_usedOnly_1599_);
v___x_99359__boxed_1615_ = lean_unbox(v___x_1600_);
v___x_99360__boxed_1616_ = lean_unbox(v___x_1601_);
v_res_1617_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1594_, v_a_1595_, v_zeta_boxed_1612_, v___y_99358__boxed_1613_, v_x_1598_, v_usedOnly_boxed_1614_, v___x_99359__boxed_1615_, v___x_99360__boxed_1616_, v_snd_1602_, v_h_x27_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
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
uint8_t v_zeta_boxed_1687_; uint8_t v_usedOnly_boxed_1688_; uint8_t v___x_99513__boxed_1689_; uint8_t v___y_99515__boxed_1690_; uint8_t v___x_99516__boxed_1691_; lean_object* v_res_1692_; 
v_zeta_boxed_1687_ = lean_unbox(v_zeta_1672_);
v_usedOnly_boxed_1688_ = lean_unbox(v_usedOnly_1674_);
v___x_99513__boxed_1689_ = lean_unbox(v___x_1675_);
v___y_99515__boxed_1690_ = lean_unbox(v___y_1677_);
v___x_99516__boxed_1691_ = lean_unbox(v___x_1678_);
v_res_1692_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1670_, v_a_1671_, v_zeta_boxed_1687_, v_x_1673_, v_usedOnly_boxed_1688_, v___x_99513__boxed_1689_, v_snd_1676_, v___y_99515__boxed_1690_, v___x_99516__boxed_1691_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
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
uint8_t v_zeta_boxed_1749_; uint8_t v_usedOnly_boxed_1750_; uint8_t v___x_99626__boxed_1751_; uint8_t v___y_99628__boxed_1752_; uint8_t v___x_99629__boxed_1753_; lean_object* v_res_1754_; 
v_zeta_boxed_1749_ = lean_unbox(v_zeta_1732_);
v_usedOnly_boxed_1750_ = lean_unbox(v_usedOnly_1733_);
v___x_99626__boxed_1751_ = lean_unbox(v___x_1734_);
v___y_99628__boxed_1752_ = lean_unbox(v___y_1736_);
v___x_99629__boxed_1753_ = lean_unbox(v___x_1737_);
v_res_1754_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1729_, v_eq_x3f_1730_, v_a_1731_, v_zeta_boxed_1749_, v_usedOnly_boxed_1750_, v___x_99626__boxed_1751_, v_snd_1735_, v___y_99628__boxed_1752_, v___x_99629__boxed_1753_, v_letOrReassign_1738_, v_a_1739_, v_x_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
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
uint8_t v___x_99700__boxed_1777_; lean_object* v_res_1778_; 
v___x_99700__boxed_1777_ = lean_unbox(v___x_1767_);
v_res_1778_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99700__boxed_1777_, v_____do__lift_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
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
uint8_t v___x_99735__boxed_1804_; lean_object* v_res_1805_; 
v___x_99735__boxed_1804_ = lean_unbox(v___x_1794_);
v_res_1805_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1792_, v___x_1793_, v___x_99735__boxed_1804_, v___x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
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
v___x_1868_ = lean_st_ref_set(v___y_1826_, v___x_1867_);
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
v___x_1936_ = lean_st_ref_set(v___y_1907_, v___x_1935_);
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
uint8_t v___x_100264__boxed_2333_; uint8_t v___x_100266__boxed_2334_; lean_object* v_res_2335_; 
v___x_100264__boxed_2333_ = lean_unbox(v___x_2315_);
v___x_100266__boxed_2334_ = lean_unbox(v___x_2318_);
v_res_2335_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2314_, v___x_100264__boxed_2333_, v_config_2316_, v_a_2317_, v___x_100266__boxed_2334_, v___x_2319_, v___x_2320_, v___x_2321_, v___f_2322_, v___x_2323_, v_body_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2412_, lean_object* v_currNamespace_2413_, lean_object* v_openDecls_2414_, lean_object* v_n_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = l_Lean_ResolveName_resolveNamespace(v_env_2412_, v_currNamespace_2413_, v_openDecls_2414_, v_n_2415_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v___y_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2420_, lean_object* v_currNamespace_2421_, lean_object* v_openDecls_2422_, lean_object* v_n_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2420_, v_currNamespace_2421_, v_openDecls_2422_, v_n_2423_, v___y_2424_, v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2427_, lean_object* v_declName_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_2431_; lean_object* v_env_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; uint8_t v___x_2435_; 
v___x_2431_ = 0;
v_env_2432_ = l_Lean_Environment_setExporting(v_env_2427_, v___x_2431_);
lean_inc(v_declName_2428_);
v___x_2433_ = l_Lean_mkPrivateName(v_env_2432_, v_declName_2428_);
v___x_2434_ = 1;
lean_inc_ref(v_env_2432_);
v___x_2435_ = l_Lean_Environment_contains(v_env_2432_, v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2436_ = l_Lean_privateToUserName(v_declName_2428_);
v___x_2437_ = l_Lean_Environment_contains(v_env_2432_, v___x_2436_, v___x_2434_);
v___x_2438_ = lean_box(v___x_2437_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___y_2430_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec_ref(v_env_2432_);
lean_dec(v_declName_2428_);
v___x_2440_ = lean_box(v___x_2435_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___y_2430_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2442_, lean_object* v_declName_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2442_, v_declName_2443_, v___y_2444_, v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2446_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2447_; double v___x_2448_; 
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = lean_float_of_nat(v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2451_, lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_ref_2458_; lean_object* v___x_2459_; lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2504_; 
v_ref_2458_ = lean_ctor_get(v___y_2455_, 5);
v___x_2459_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2504_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2504_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v_traceState_2465_; lean_object* v_env_2466_; lean_object* v_nextMacroScope_2467_; lean_object* v_ngen_2468_; lean_object* v_auxDeclNGen_2469_; lean_object* v_cache_2470_; lean_object* v_messages_2471_; lean_object* v_infoState_2472_; lean_object* v_snapshotTasks_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2503_; 
v___x_2464_ = lean_st_ref_take(v___y_2456_);
v_traceState_2465_ = lean_ctor_get(v___x_2464_, 4);
v_env_2466_ = lean_ctor_get(v___x_2464_, 0);
v_nextMacroScope_2467_ = lean_ctor_get(v___x_2464_, 1);
v_ngen_2468_ = lean_ctor_get(v___x_2464_, 2);
v_auxDeclNGen_2469_ = lean_ctor_get(v___x_2464_, 3);
v_cache_2470_ = lean_ctor_get(v___x_2464_, 5);
v_messages_2471_ = lean_ctor_get(v___x_2464_, 6);
v_infoState_2472_ = lean_ctor_get(v___x_2464_, 7);
v_snapshotTasks_2473_ = lean_ctor_get(v___x_2464_, 8);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2475_ = v___x_2464_;
v_isShared_2476_ = v_isSharedCheck_2503_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snapshotTasks_2473_);
lean_inc(v_infoState_2472_);
lean_inc(v_messages_2471_);
lean_inc(v_cache_2470_);
lean_inc(v_traceState_2465_);
lean_inc(v_auxDeclNGen_2469_);
lean_inc(v_ngen_2468_);
lean_inc(v_nextMacroScope_2467_);
lean_inc(v_env_2466_);
lean_dec(v___x_2464_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2503_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
uint64_t v_tid_2477_; lean_object* v_traces_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2502_; 
v_tid_2477_ = lean_ctor_get_uint64(v_traceState_2465_, sizeof(void*)*1);
v_traces_2478_ = lean_ctor_get(v_traceState_2465_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_traceState_2465_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2480_ = v_traceState_2465_;
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_traces_2478_);
lean_dec(v_traceState_2465_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; double v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2484_ = 0;
v___x_2485_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2486_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2486_, 0, v_cls_2451_);
lean_ctor_set(v___x_2486_, 1, v___x_2482_);
lean_ctor_set(v___x_2486_, 2, v___x_2485_);
lean_ctor_set_float(v___x_2486_, sizeof(void*)*3, v___x_2483_);
lean_ctor_set_float(v___x_2486_, sizeof(void*)*3 + 8, v___x_2483_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*3 + 16, v___x_2484_);
v___x_2487_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2488_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v_a_2460_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
lean_inc(v_ref_2458_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_ref_2458_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_PersistentArray_push___redArg(v_traces_2478_, v___x_2489_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2490_);
v___x_2492_ = v___x_2480_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2490_);
lean_ctor_set_uint64(v_reuseFailAlloc_2501_, sizeof(void*)*1, v_tid_2477_);
v___x_2492_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 4, v___x_2492_);
v___x_2494_ = v___x_2475_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_env_2466_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_nextMacroScope_2467_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_ngen_2468_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_auxDeclNGen_2469_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2500_, 5, v_cache_2470_);
lean_ctor_set(v_reuseFailAlloc_2500_, 6, v_messages_2471_);
lean_ctor_set(v_reuseFailAlloc_2500_, 7, v_infoState_2472_);
lean_ctor_set(v_reuseFailAlloc_2500_, 8, v_snapshotTasks_2473_);
v___x_2494_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2495_ = lean_st_ref_set(v___y_2456_, v___x_2494_);
v___x_2496_ = lean_box(0);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2496_);
v___x_2498_ = v___x_2462_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2505_, lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2505_, v_msg_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
if (lean_obj_tag(v_as_2516_) == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
else
{
lean_object* v_options_2527_; uint8_t v_hasTrace_2528_; 
v_options_2527_ = lean_ctor_get(v___y_2522_, 2);
v_hasTrace_2528_ = lean_ctor_get_uint8(v_options_2527_, sizeof(void*)*1);
if (v_hasTrace_2528_ == 0)
{
lean_object* v_tail_2529_; 
v_tail_2529_ = lean_ctor_get(v_as_2516_, 1);
lean_inc(v_tail_2529_);
lean_dec_ref_known(v_as_2516_, 2);
v_as_2516_ = v_tail_2529_;
goto _start;
}
else
{
lean_object* v_head_2531_; lean_object* v_tail_2532_; lean_object* v_fst_2533_; lean_object* v_snd_2534_; lean_object* v_inheritedTraceOptions_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_head_2531_ = lean_ctor_get(v_as_2516_, 0);
lean_inc(v_head_2531_);
v_tail_2532_ = lean_ctor_get(v_as_2516_, 1);
lean_inc(v_tail_2532_);
lean_dec_ref_known(v_as_2516_, 2);
v_fst_2533_ = lean_ctor_get(v_head_2531_, 0);
lean_inc_n(v_fst_2533_, 2);
v_snd_2534_ = lean_ctor_get(v_head_2531_, 1);
lean_inc(v_snd_2534_);
lean_dec(v_head_2531_);
v_inheritedTraceOptions_2535_ = lean_ctor_get(v___y_2522_, 13);
v___x_2536_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2537_ = l_Lean_Name_append(v___x_2536_, v_fst_2533_);
v___x_2538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2535_, v_options_2527_, v___x_2537_);
lean_dec(v___x_2537_);
if (v___x_2538_ == 0)
{
lean_dec(v_snd_2534_);
lean_dec(v_fst_2533_);
v_as_2516_ = v_tail_2532_;
goto _start;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_snd_2534_);
v___x_2541_ = l_Lean_MessageData_ofFormat(v___x_2540_);
v___x_2542_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2533_, v___x_2541_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref_known(v___x_2542_, 1);
v_as_2516_ = v_tail_2532_;
goto _start;
}
else
{
lean_dec(v_tail_2532_);
return v___x_2542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2553_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2554_, lean_object* v_i_2555_, lean_object* v_k_2556_){
_start:
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = lean_array_get_size(v_keys_2554_);
v___x_2558_ = lean_nat_dec_lt(v_i_2555_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_dec(v_i_2555_);
return v___x_2558_;
}
else
{
lean_object* v_k_x27_2559_; uint8_t v___x_2560_; 
v_k_x27_2559_ = lean_array_fget_borrowed(v_keys_2554_, v_i_2555_);
v___x_2560_ = l_Lean_instBEqExtraModUse_beq(v_k_2556_, v_k_x27_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = lean_nat_add(v_i_2555_, v___x_2561_);
lean_dec(v_i_2555_);
v_i_2555_ = v___x_2562_;
goto _start;
}
else
{
lean_dec(v_i_2555_);
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2564_, lean_object* v_i_2565_, lean_object* v_k_2566_){
_start:
{
uint8_t v_res_2567_; lean_object* v_r_2568_; 
v_res_2567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2564_, v_i_2565_, v_k_2566_);
lean_dec_ref(v_k_2566_);
lean_dec_ref(v_keys_2564_);
v_r_2568_ = lean_box(v_res_2567_);
return v_r_2568_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2569_, size_t v_x_2570_, lean_object* v_x_2571_){
_start:
{
if (lean_obj_tag(v_x_2569_) == 0)
{
lean_object* v_es_2572_; lean_object* v___x_2573_; size_t v___x_2574_; size_t v___x_2575_; lean_object* v_j_2576_; lean_object* v___x_2577_; 
v_es_2572_ = lean_ctor_get(v_x_2569_, 0);
v___x_2573_ = lean_box(2);
v___x_2574_ = ((size_t)31ULL);
v___x_2575_ = lean_usize_land(v_x_2570_, v___x_2574_);
v_j_2576_ = lean_usize_to_nat(v___x_2575_);
v___x_2577_ = lean_array_get_borrowed(v___x_2573_, v_es_2572_, v_j_2576_);
lean_dec(v_j_2576_);
switch(lean_obj_tag(v___x_2577_))
{
case 0:
{
lean_object* v_key_2578_; uint8_t v___x_2579_; 
v_key_2578_ = lean_ctor_get(v___x_2577_, 0);
v___x_2579_ = l_Lean_instBEqExtraModUse_beq(v_x_2571_, v_key_2578_);
return v___x_2579_;
}
case 1:
{
lean_object* v_node_2580_; size_t v___x_2581_; size_t v___x_2582_; 
v_node_2580_ = lean_ctor_get(v___x_2577_, 0);
v___x_2581_ = ((size_t)5ULL);
v___x_2582_ = lean_usize_shift_right(v_x_2570_, v___x_2581_);
v_x_2569_ = v_node_2580_;
v_x_2570_ = v___x_2582_;
goto _start;
}
default: 
{
uint8_t v___x_2584_; 
v___x_2584_ = 0;
return v___x_2584_;
}
}
}
else
{
lean_object* v_ks_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_ks_2585_ = lean_ctor_get(v_x_2569_, 0);
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2585_, v___x_2586_, v_x_2571_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
size_t v_x_101008__boxed_2591_; uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_x_101008__boxed_2591_ = lean_unbox_usize(v_x_2589_);
lean_dec(v_x_2589_);
v_res_2592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2588_, v_x_101008__boxed_2591_, v_x_2590_);
lean_dec_ref(v_x_2590_);
lean_dec_ref(v_x_2588_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2594_, lean_object* v_x_2595_){
_start:
{
uint64_t v___x_2596_; size_t v___x_2597_; uint8_t v___x_2598_; 
v___x_2596_ = l_Lean_instHashableExtraModUse_hash(v_x_2595_);
v___x_2597_ = lean_uint64_to_usize(v___x_2596_);
v___x_2598_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2594_, v___x_2597_, v_x_2595_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2599_, lean_object* v_x_2600_){
_start:
{
uint8_t v_res_2601_; lean_object* v_r_2602_; 
v_res_2601_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2599_, v_x_2600_);
lean_dec_ref(v_x_2600_);
lean_dec_ref(v_x_2599_);
v_r_2602_ = lean_box(v_res_2601_);
return v_r_2602_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2607_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2606_, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2608_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2614_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
lean_ctor_set(v___x_2614_, 2, v___x_2613_);
lean_ctor_set(v___x_2614_, 3, v___x_2613_);
lean_ctor_set(v___x_2614_, 4, v___x_2613_);
lean_ctor_set(v___x_2614_, 5, v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2620_ = l_Lean_stringToMessageData(v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_cls_2626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2627_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2628_ = l_Lean_Name_append(v___x_2627_, v_cls_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2639_, uint8_t v_isMeta_2640_, lean_object* v_hint_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v_env_2651_; uint8_t v_isExporting_2652_; lean_object* v___x_2653_; lean_object* v_env_2654_; lean_object* v___x_2655_; lean_object* v_entry_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2650_ = lean_st_ref_get(v___y_2648_);
v_env_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_ref(v_env_2651_);
lean_dec(v___x_2650_);
v_isExporting_2652_ = lean_ctor_get_uint8(v_env_2651_, sizeof(void*)*8);
lean_dec_ref(v_env_2651_);
v___x_2653_ = lean_st_ref_get(v___y_2648_);
v_env_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc_ref(v_env_2654_);
lean_dec(v___x_2653_);
v___x_2655_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2639_);
v_entry_2656_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2656_, 0, v_mod_2639_);
lean_ctor_set_uint8(v_entry_2656_, sizeof(void*)*1, v_isExporting_2652_);
lean_ctor_set_uint8(v_entry_2656_, sizeof(void*)*1 + 1, v_isMeta_2640_);
v___x_2657_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2658_ = lean_box(1);
v___x_2659_ = lean_box(0);
v___x_2702_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2655_, v___x_2657_, v_env_2654_, v___x_2658_, v___x_2659_);
v___x_2703_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2702_, v_entry_2656_);
lean_dec(v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v_options_2704_; uint8_t v_hasTrace_2705_; 
v_options_2704_ = lean_ctor_get(v___y_2647_, 2);
v_hasTrace_2705_ = lean_ctor_get_uint8(v_options_2704_, sizeof(void*)*1);
if (v_hasTrace_2705_ == 0)
{
lean_dec(v_hint_2641_);
lean_dec(v_mod_2639_);
v___y_2661_ = v___y_2646_;
v___y_2662_ = v___y_2648_;
goto v___jp_2660_;
}
else
{
lean_object* v_inheritedTraceOptions_2706_; lean_object* v_cls_2707_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_inheritedTraceOptions_2706_ = lean_ctor_get(v___y_2647_, 13);
v_cls_2707_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2727_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2706_, v_options_2704_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec(v_hint_2641_);
lean_dec(v_mod_2639_);
v___y_2661_ = v___y_2646_;
v___y_2662_ = v___y_2648_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2729_; lean_object* v___y_2731_; 
v___x_2729_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2652_ == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2731_ = v___x_2738_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2739_; 
v___x_2739_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2731_ = v___x_2739_;
goto v___jp_2730_;
}
v___jp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_inc_ref(v___y_2731_);
v___x_2732_ = l_Lean_stringToMessageData(v___y_2731_);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2729_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
if (v_isMeta_2640_ == 0)
{
lean_object* v___x_2736_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2714_ = v___x_2735_;
v___y_2715_ = v___x_2736_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2737_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2714_ = v___x_2735_;
v___y_2715_ = v___x_2737_;
goto v___jp_2713_;
}
}
}
v___jp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___y_2709_);
lean_ctor_set(v___x_2711_, 1, v___y_2710_);
v___x_2712_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2707_, v___x_2711_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_dec_ref_known(v___x_2712_, 1);
v___y_2661_ = v___y_2646_;
v___y_2662_ = v___y_2648_;
goto v___jp_2660_;
}
else
{
lean_dec_ref_known(v_entry_2656_, 1);
return v___x_2712_;
}
}
v___jp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
lean_inc_ref(v___y_2715_);
v___x_2716_ = l_Lean_stringToMessageData(v___y_2715_);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2714_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_MessageData_ofName(v_mod_2639_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_Name_isAnonymous(v_hint_2641_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2724_ = l_Lean_MessageData_ofName(v_hint_2641_);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___y_2709_ = v___x_2721_;
v___y_2710_ = v___x_2725_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2726_; 
lean_dec(v_hint_2641_);
v___x_2726_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2709_ = v___x_2721_;
v___y_2710_ = v___x_2726_;
goto v___jp_2708_;
}
}
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec_ref_known(v_entry_2656_, 1);
lean_dec(v_hint_2641_);
lean_dec(v_mod_2639_);
v___x_2740_ = lean_box(0);
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
v___jp_2660_:
{
lean_object* v___x_2663_; lean_object* v_toEnvExtension_2664_; lean_object* v_env_2665_; lean_object* v_nextMacroScope_2666_; lean_object* v_ngen_2667_; lean_object* v_auxDeclNGen_2668_; lean_object* v_traceState_2669_; lean_object* v_messages_2670_; lean_object* v_infoState_2671_; lean_object* v_snapshotTasks_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2700_; 
v___x_2663_ = lean_st_ref_take(v___y_2662_);
v_toEnvExtension_2664_ = lean_ctor_get(v___x_2657_, 0);
v_env_2665_ = lean_ctor_get(v___x_2663_, 0);
v_nextMacroScope_2666_ = lean_ctor_get(v___x_2663_, 1);
v_ngen_2667_ = lean_ctor_get(v___x_2663_, 2);
v_auxDeclNGen_2668_ = lean_ctor_get(v___x_2663_, 3);
v_traceState_2669_ = lean_ctor_get(v___x_2663_, 4);
v_messages_2670_ = lean_ctor_get(v___x_2663_, 6);
v_infoState_2671_ = lean_ctor_get(v___x_2663_, 7);
v_snapshotTasks_2672_ = lean_ctor_get(v___x_2663_, 8);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2663_, 5);
lean_dec(v_unused_2701_);
v___x_2674_ = v___x_2663_;
v_isShared_2675_ = v_isSharedCheck_2700_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_snapshotTasks_2672_);
lean_inc(v_infoState_2671_);
lean_inc(v_messages_2670_);
lean_inc(v_traceState_2669_);
lean_inc(v_auxDeclNGen_2668_);
lean_inc(v_ngen_2667_);
lean_inc(v_nextMacroScope_2666_);
lean_inc(v_env_2665_);
lean_dec(v___x_2663_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2700_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_asyncMode_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v_asyncMode_2676_ = lean_ctor_get(v_toEnvExtension_2664_, 2);
v___x_2677_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2657_, v_env_2665_, v_entry_2656_, v_asyncMode_2676_, v___x_2659_);
v___x_2678_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 5, v___x_2678_);
lean_ctor_set(v___x_2674_, 0, v___x_2677_);
v___x_2680_ = v___x_2674_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_nextMacroScope_2666_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_ngen_2667_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_auxDeclNGen_2668_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v_traceState_2669_);
lean_ctor_set(v_reuseFailAlloc_2699_, 5, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2699_, 6, v_messages_2670_);
lean_ctor_set(v_reuseFailAlloc_2699_, 7, v_infoState_2671_);
lean_ctor_set(v_reuseFailAlloc_2699_, 8, v_snapshotTasks_2672_);
v___x_2680_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_mctx_2683_; lean_object* v_zetaDeltaFVarIds_2684_; lean_object* v_postponed_2685_; lean_object* v_diag_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2697_; 
v___x_2681_ = lean_st_ref_set(v___y_2662_, v___x_2680_);
v___x_2682_ = lean_st_ref_take(v___y_2661_);
v_mctx_2683_ = lean_ctor_get(v___x_2682_, 0);
v_zetaDeltaFVarIds_2684_ = lean_ctor_get(v___x_2682_, 2);
v_postponed_2685_ = lean_ctor_get(v___x_2682_, 3);
v_diag_2686_ = lean_ctor_get(v___x_2682_, 4);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v___x_2682_, 1);
lean_dec(v_unused_2698_);
v___x_2688_ = v___x_2682_;
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_diag_2686_);
lean_inc(v_postponed_2685_);
lean_inc(v_zetaDeltaFVarIds_2684_);
lean_inc(v_mctx_2683_);
lean_dec(v___x_2682_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_mctx_2683_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_zetaDeltaFVarIds_2684_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_postponed_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_diag_2686_);
v___x_2692_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_st_ref_set(v___y_2661_, v___x_2692_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2742_, lean_object* v_isMeta_2743_, lean_object* v_hint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v_isMeta_boxed_2753_; lean_object* v_res_2754_; 
v_isMeta_boxed_2753_ = lean_unbox(v_isMeta_2743_);
v_res_2754_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2742_, v_isMeta_boxed_2753_, v_hint_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2755_, lean_object* v_declName_2756_, lean_object* v_as_2757_, size_t v_sz_2758_, size_t v_i_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_usize_dec_lt(v_i_2759_, v_sz_2758_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec(v_declName_2756_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_b_2760_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v_modules_2772_; lean_object* v___x_2773_; lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v_toImport_2776_; lean_object* v_module_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2771_ = l_Lean_Environment_header(v___x_2755_);
v_modules_2772_ = lean_ctor_get(v___x_2771_, 3);
lean_inc_ref(v_modules_2772_);
lean_dec_ref(v___x_2771_);
v___x_2773_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2774_ = lean_array_uget_borrowed(v_as_2757_, v_i_2759_);
v___x_2775_ = lean_array_get(v___x_2773_, v_modules_2772_, v_a_2774_);
lean_dec_ref(v_modules_2772_);
v_toImport_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc_ref(v_toImport_2776_);
lean_dec(v___x_2775_);
v_module_2777_ = lean_ctor_get(v_toImport_2776_, 0);
lean_inc(v_module_2777_);
lean_dec_ref(v_toImport_2776_);
v___x_2778_ = 0;
lean_inc(v_declName_2756_);
v___x_2779_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2777_, v___x_2778_, v_declName_2756_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; 
lean_dec_ref_known(v___x_2779_, 1);
v___x_2780_ = lean_box(0);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2759_, v___x_2781_);
v_i_2759_ = v___x_2782_;
v_b_2760_ = v___x_2780_;
goto _start;
}
else
{
lean_dec(v_declName_2756_);
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2784_, lean_object* v_declName_2785_, lean_object* v_as_2786_, lean_object* v_sz_2787_, lean_object* v_i_2788_, lean_object* v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
size_t v_sz_boxed_2798_; size_t v_i_boxed_2799_; lean_object* v_res_2800_; 
v_sz_boxed_2798_ = lean_unbox_usize(v_sz_2787_);
lean_dec(v_sz_2787_);
v_i_boxed_2799_ = lean_unbox_usize(v_i_2788_);
lean_dec(v_i_2788_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2784_, v_declName_2785_, v_as_2786_, v_sz_boxed_2798_, v_i_boxed_2799_, v_b_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_as_2786_);
lean_dec_ref(v___x_2784_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_a_2801_, lean_object* v_x_2802_){
_start:
{
if (lean_obj_tag(v_x_2802_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_box(0);
return v___x_2803_;
}
else
{
lean_object* v_key_2804_; lean_object* v_value_2805_; lean_object* v_tail_2806_; uint8_t v___x_2807_; 
v_key_2804_ = lean_ctor_get(v_x_2802_, 0);
v_value_2805_ = lean_ctor_get(v_x_2802_, 1);
v_tail_2806_ = lean_ctor_get(v_x_2802_, 2);
v___x_2807_ = lean_name_eq(v_key_2804_, v_a_2801_);
if (v___x_2807_ == 0)
{
v_x_2802_ = v_tail_2806_;
goto _start;
}
else
{
lean_object* v___x_2809_; 
lean_inc(v_value_2805_);
v___x_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_value_2805_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_2810_, lean_object* v_x_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2810_, v_x_2811_);
lean_dec(v_x_2811_);
lean_dec(v_a_2810_);
return v_res_2812_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2813_; uint64_t v___x_2814_; 
v___x_2813_ = lean_unsigned_to_nat(1723u);
v___x_2814_ = lean_uint64_of_nat(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_buckets_2817_; lean_object* v___x_2818_; uint64_t v___y_2820_; 
v_buckets_2817_ = lean_ctor_get(v_m_2815_, 1);
v___x_2818_ = lean_array_get_size(v_buckets_2817_);
if (lean_obj_tag(v_a_2816_) == 0)
{
uint64_t v___x_2834_; 
v___x_2834_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0);
v___y_2820_ = v___x_2834_;
goto v___jp_2819_;
}
else
{
uint64_t v_hash_2835_; 
v_hash_2835_ = lean_ctor_get_uint64(v_a_2816_, sizeof(void*)*2);
v___y_2820_ = v_hash_2835_;
goto v___jp_2819_;
}
v___jp_2819_:
{
uint64_t v___x_2821_; uint64_t v___x_2822_; uint64_t v_fold_2823_; uint64_t v___x_2824_; uint64_t v___x_2825_; uint64_t v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; size_t v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2821_ = 32ULL;
v___x_2822_ = lean_uint64_shift_right(v___y_2820_, v___x_2821_);
v_fold_2823_ = lean_uint64_xor(v___y_2820_, v___x_2822_);
v___x_2824_ = 16ULL;
v___x_2825_ = lean_uint64_shift_right(v_fold_2823_, v___x_2824_);
v___x_2826_ = lean_uint64_xor(v_fold_2823_, v___x_2825_);
v___x_2827_ = lean_uint64_to_usize(v___x_2826_);
v___x_2828_ = lean_usize_of_nat(v___x_2818_);
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_sub(v___x_2828_, v___x_2829_);
v___x_2831_ = lean_usize_land(v___x_2827_, v___x_2830_);
v___x_2832_ = lean_array_uget_borrowed(v_buckets_2817_, v___x_2831_);
v___x_2833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2816_, v___x_2832_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_m_2836_);
return v_res_2838_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2842_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2843_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2842_, v___x_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2846_, uint8_t v_isMeta_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v_env_2860_; lean_object* v___y_2862_; lean_object* v___x_2875_; 
v___x_2856_ = lean_st_ref_get(v___y_2854_);
v_env_2860_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_ref(v_env_2860_);
lean_dec(v___x_2856_);
v___x_2875_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2860_, v_declName_2846_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref(v_env_2860_);
lean_dec(v_declName_2846_);
goto v___jp_2857_;
}
else
{
lean_object* v_val_2876_; lean_object* v___x_2877_; lean_object* v_modules_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v_val_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = l_Lean_Environment_header(v_env_2860_);
v_modules_2878_ = lean_ctor_get(v___x_2877_, 3);
lean_inc_ref(v_modules_2878_);
lean_dec_ref(v___x_2877_);
v___x_2879_ = lean_array_get_size(v_modules_2878_);
v___x_2880_ = lean_nat_dec_lt(v_val_2876_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_dec_ref(v_modules_2878_);
lean_dec(v_val_2876_);
lean_dec_ref(v_env_2860_);
lean_dec(v_declName_2846_);
goto v___jp_2857_;
}
else
{
lean_object* v___x_2881_; lean_object* v_env_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___y_2886_; 
v___x_2881_ = lean_st_ref_get(v___y_2854_);
v_env_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc_ref(v_env_2882_);
lean_dec(v___x_2881_);
v___x_2883_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2884_ = lean_array_fget(v_modules_2878_, v_val_2876_);
lean_dec(v_val_2876_);
lean_dec_ref(v_modules_2878_);
if (v_isMeta_2847_ == 0)
{
lean_dec_ref(v_env_2882_);
v___y_2886_ = v_isMeta_2847_;
goto v___jp_2885_;
}
else
{
uint8_t v___x_2897_; 
lean_inc(v_declName_2846_);
v___x_2897_ = l_Lean_isMarkedMeta(v_env_2882_, v_declName_2846_);
if (v___x_2897_ == 0)
{
v___y_2886_ = v_isMeta_2847_;
goto v___jp_2885_;
}
else
{
uint8_t v___x_2898_; 
v___x_2898_ = 0;
v___y_2886_ = v___x_2898_;
goto v___jp_2885_;
}
}
v___jp_2885_:
{
lean_object* v_toImport_2887_; lean_object* v_module_2888_; lean_object* v___x_2889_; 
v_toImport_2887_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_toImport_2887_);
lean_dec(v___x_2884_);
v_module_2888_ = lean_ctor_get(v_toImport_2887_, 0);
lean_inc(v_module_2888_);
lean_dec_ref(v_toImport_2887_);
lean_inc(v_declName_2846_);
v___x_2889_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2888_, v___y_2886_, v_declName_2846_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2889_, 1);
v___x_2890_ = l_Lean_indirectModUseExt;
v___x_2891_ = lean_box(1);
v___x_2892_ = lean_box(0);
lean_inc_ref(v_env_2860_);
v___x_2893_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2883_, v___x_2890_, v_env_2860_, v___x_2891_, v___x_2892_);
v___x_2894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_2893_, v_declName_2846_);
lean_dec(v___x_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2862_ = v___x_2895_;
goto v___jp_2861_;
}
else
{
lean_object* v_val_2896_; 
v_val_2896_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v___x_2894_, 1);
v___y_2862_ = v_val_2896_;
goto v___jp_2861_;
}
}
else
{
lean_dec_ref(v_env_2860_);
lean_dec(v_declName_2846_);
return v___x_2889_;
}
}
}
}
v___jp_2857_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
v___jp_2861_:
{
lean_object* v___x_2863_; size_t v_sz_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_box(0);
v_sz_2864_ = lean_array_size(v___y_2862_);
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2860_, v_declName_2846_, v___y_2862_, v_sz_2864_, v___x_2865_, v___x_2863_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_env_2860_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v___x_2866_, 0);
lean_dec(v_unused_2874_);
v___x_2868_ = v___x_2866_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v___x_2866_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2863_);
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2863_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
return v___x_2866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2899_, lean_object* v_isMeta_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
uint8_t v_isMeta_boxed_2909_; lean_object* v_res_2910_; 
v_isMeta_boxed_2909_ = lean_unbox(v_isMeta_2900_);
v_res_2910_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2899_, v_isMeta_boxed_2909_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
if (lean_obj_tag(v_as_x27_2911_) == 0)
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_b_2912_);
return v___x_2921_;
}
else
{
lean_object* v_head_2922_; lean_object* v_tail_2923_; uint8_t v___x_2924_; lean_object* v___x_2925_; 
v_head_2922_ = lean_ctor_get(v_as_x27_2911_, 0);
v_tail_2923_ = lean_ctor_get(v_as_x27_2911_, 1);
v___x_2924_ = 1;
lean_inc(v_head_2922_);
v___x_2925_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2922_, v___x_2924_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2926_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2926_ = lean_box(0);
v_as_x27_2911_ = v_tail_2923_;
v_b_2912_ = v___x_2926_;
goto _start;
}
else
{
return v___x_2925_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2928_, lean_object* v_b_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2928_, v_b_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v_as_x27_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2939_, lean_object* v_options_2940_, lean_object* v_currNamespace_2941_, lean_object* v_openDecls_2942_, lean_object* v_n_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = l_Lean_ResolveName_resolveGlobalName(v_env_2939_, v_options_2940_, v_currNamespace_2941_, v_openDecls_2942_, v_n_2943_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___y_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2948_, lean_object* v_options_2949_, lean_object* v_currNamespace_2950_, lean_object* v_openDecls_2951_, lean_object* v_n_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2948_, v_options_2949_, v_currNamespace_2950_, v_openDecls_2951_, v_n_2952_, v___y_2953_, v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec_ref(v_options_2949_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_2956_, lean_object* v_msg_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_fileName_2963_; lean_object* v_fileMap_2964_; lean_object* v_options_2965_; lean_object* v_currRecDepth_2966_; lean_object* v_maxRecDepth_2967_; lean_object* v_ref_2968_; lean_object* v_currNamespace_2969_; lean_object* v_openDecls_2970_; lean_object* v_initHeartbeats_2971_; lean_object* v_maxHeartbeats_2972_; lean_object* v_quotContext_2973_; lean_object* v_currMacroScope_2974_; uint8_t v_diag_2975_; lean_object* v_cancelTk_x3f_2976_; uint8_t v_suppressElabErrors_2977_; lean_object* v_inheritedTraceOptions_2978_; lean_object* v_ref_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_fileName_2963_ = lean_ctor_get(v___y_2960_, 0);
v_fileMap_2964_ = lean_ctor_get(v___y_2960_, 1);
v_options_2965_ = lean_ctor_get(v___y_2960_, 2);
v_currRecDepth_2966_ = lean_ctor_get(v___y_2960_, 3);
v_maxRecDepth_2967_ = lean_ctor_get(v___y_2960_, 4);
v_ref_2968_ = lean_ctor_get(v___y_2960_, 5);
v_currNamespace_2969_ = lean_ctor_get(v___y_2960_, 6);
v_openDecls_2970_ = lean_ctor_get(v___y_2960_, 7);
v_initHeartbeats_2971_ = lean_ctor_get(v___y_2960_, 8);
v_maxHeartbeats_2972_ = lean_ctor_get(v___y_2960_, 9);
v_quotContext_2973_ = lean_ctor_get(v___y_2960_, 10);
v_currMacroScope_2974_ = lean_ctor_get(v___y_2960_, 11);
v_diag_2975_ = lean_ctor_get_uint8(v___y_2960_, sizeof(void*)*14);
v_cancelTk_x3f_2976_ = lean_ctor_get(v___y_2960_, 12);
v_suppressElabErrors_2977_ = lean_ctor_get_uint8(v___y_2960_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2978_ = lean_ctor_get(v___y_2960_, 13);
v_ref_2979_ = l_Lean_replaceRef(v_ref_2956_, v_ref_2968_);
lean_inc_ref(v_inheritedTraceOptions_2978_);
lean_inc(v_cancelTk_x3f_2976_);
lean_inc(v_currMacroScope_2974_);
lean_inc(v_quotContext_2973_);
lean_inc(v_maxHeartbeats_2972_);
lean_inc(v_initHeartbeats_2971_);
lean_inc(v_openDecls_2970_);
lean_inc(v_currNamespace_2969_);
lean_inc(v_maxRecDepth_2967_);
lean_inc(v_currRecDepth_2966_);
lean_inc_ref(v_options_2965_);
lean_inc_ref(v_fileMap_2964_);
lean_inc_ref(v_fileName_2963_);
v___x_2980_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2980_, 0, v_fileName_2963_);
lean_ctor_set(v___x_2980_, 1, v_fileMap_2964_);
lean_ctor_set(v___x_2980_, 2, v_options_2965_);
lean_ctor_set(v___x_2980_, 3, v_currRecDepth_2966_);
lean_ctor_set(v___x_2980_, 4, v_maxRecDepth_2967_);
lean_ctor_set(v___x_2980_, 5, v_ref_2979_);
lean_ctor_set(v___x_2980_, 6, v_currNamespace_2969_);
lean_ctor_set(v___x_2980_, 7, v_openDecls_2970_);
lean_ctor_set(v___x_2980_, 8, v_initHeartbeats_2971_);
lean_ctor_set(v___x_2980_, 9, v_maxHeartbeats_2972_);
lean_ctor_set(v___x_2980_, 10, v_quotContext_2973_);
lean_ctor_set(v___x_2980_, 11, v_currMacroScope_2974_);
lean_ctor_set(v___x_2980_, 12, v_cancelTk_x3f_2976_);
lean_ctor_set(v___x_2980_, 13, v_inheritedTraceOptions_2978_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*14, v_diag_2975_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*14 + 1, v_suppressElabErrors_2977_);
v___x_2981_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_2957_, v___y_2958_, v___y_2959_, v___x_2980_, v___y_2961_);
lean_dec_ref_known(v___x_2980_, 14);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2982_, lean_object* v_msg_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_2982_, v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v_ref_2982_);
return v_res_2989_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = l_Lean_maxRecDepthErrorMessage;
v___x_2996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_2998_ = l_Lean_MessageData_ofFormat(v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3000_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3001_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_ref_3002_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; lean_object* v_env_3021_; lean_object* v_options_3022_; lean_object* v_currRecDepth_3023_; lean_object* v_maxRecDepth_3024_; lean_object* v_ref_3025_; lean_object* v_currNamespace_3026_; lean_object* v_openDecls_3027_; lean_object* v_quotContext_3028_; lean_object* v_currMacroScope_3029_; lean_object* v___x_3030_; lean_object* v_nextMacroScope_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v_methods_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3020_ = lean_st_ref_get(v___y_3018_);
v_env_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref_n(v_env_3021_, 4);
lean_dec(v___x_3020_);
v_options_3022_ = lean_ctor_get(v___y_3017_, 2);
v_currRecDepth_3023_ = lean_ctor_get(v___y_3017_, 3);
v_maxRecDepth_3024_ = lean_ctor_get(v___y_3017_, 4);
v_ref_3025_ = lean_ctor_get(v___y_3017_, 5);
v_currNamespace_3026_ = lean_ctor_get(v___y_3017_, 6);
v_openDecls_3027_ = lean_ctor_get(v___y_3017_, 7);
v_quotContext_3028_ = lean_ctor_get(v___y_3017_, 10);
v_currMacroScope_3029_ = lean_ctor_get(v___y_3017_, 11);
v___x_3030_ = lean_st_ref_get(v___y_3018_);
v_nextMacroScope_3031_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_nextMacroScope_3031_);
lean_dec(v___x_3030_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3032_, 0, v_env_3021_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3033_, 0, v_env_3021_);
lean_inc_n(v_openDecls_3027_, 2);
lean_inc_n(v_currNamespace_3026_, 3);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3034_, 0, v_env_3021_);
lean_closure_set(v___f_3034_, 1, v_currNamespace_3026_);
lean_closure_set(v___f_3034_, 2, v_openDecls_3027_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3035_, 0, v_currNamespace_3026_);
lean_inc_ref(v_options_3022_);
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3036_, 0, v_env_3021_);
lean_closure_set(v___f_3036_, 1, v_options_3022_);
lean_closure_set(v___f_3036_, 2, v_currNamespace_3026_);
lean_closure_set(v___f_3036_, 3, v_openDecls_3027_);
v_methods_3037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3037_, 0, v___f_3032_);
lean_ctor_set(v_methods_3037_, 1, v___f_3035_);
lean_ctor_set(v_methods_3037_, 2, v___f_3033_);
lean_ctor_set(v_methods_3037_, 3, v___f_3034_);
lean_ctor_set(v_methods_3037_, 4, v___f_3036_);
lean_inc(v_ref_3025_);
lean_inc(v_maxRecDepth_3024_);
lean_inc(v_currRecDepth_3023_);
lean_inc(v_currMacroScope_3029_);
lean_inc(v_quotContext_3028_);
v___x_3038_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3038_, 0, v_methods_3037_);
lean_ctor_set(v___x_3038_, 1, v_quotContext_3028_);
lean_ctor_set(v___x_3038_, 2, v_currMacroScope_3029_);
lean_ctor_set(v___x_3038_, 3, v_currRecDepth_3023_);
lean_ctor_set(v___x_3038_, 4, v_maxRecDepth_3024_);
lean_ctor_set(v___x_3038_, 5, v_ref_3025_);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3040_, 0, v_nextMacroScope_3031_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
v___x_3041_ = lean_apply_2(v_x_3011_, v___x_3038_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v_a_3043_; lean_object* v_macroScope_3044_; lean_object* v_traceMsgs_3045_; lean_object* v_expandedMacroDecls_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 1);
lean_inc(v_a_3042_);
v_a_3043_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3041_, 2);
v_macroScope_3044_ = lean_ctor_get(v_a_3042_, 0);
lean_inc(v_macroScope_3044_);
v_traceMsgs_3045_ = lean_ctor_get(v_a_3042_, 1);
lean_inc(v_traceMsgs_3045_);
v_expandedMacroDecls_3046_ = lean_ctor_get(v_a_3042_, 2);
lean_inc(v_expandedMacroDecls_3046_);
lean_dec(v_a_3042_);
v___x_3047_ = lean_box(0);
v___x_3048_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3046_, v___x_3047_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v_expandedMacroDecls_3046_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v_env_3050_; lean_object* v_ngen_3051_; lean_object* v_auxDeclNGen_3052_; lean_object* v_traceState_3053_; lean_object* v_cache_3054_; lean_object* v_messages_3055_; lean_object* v_infoState_3056_; lean_object* v_snapshotTasks_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref_known(v___x_3048_, 1);
v___x_3049_ = lean_st_ref_take(v___y_3018_);
v_env_3050_ = lean_ctor_get(v___x_3049_, 0);
v_ngen_3051_ = lean_ctor_get(v___x_3049_, 2);
v_auxDeclNGen_3052_ = lean_ctor_get(v___x_3049_, 3);
v_traceState_3053_ = lean_ctor_get(v___x_3049_, 4);
v_cache_3054_ = lean_ctor_get(v___x_3049_, 5);
v_messages_3055_ = lean_ctor_get(v___x_3049_, 6);
v_infoState_3056_ = lean_ctor_get(v___x_3049_, 7);
v_snapshotTasks_3057_ = lean_ctor_get(v___x_3049_, 8);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v___x_3049_, 1);
lean_dec(v_unused_3084_);
v___x_3059_ = v___x_3049_;
v_isShared_3060_ = v_isSharedCheck_3083_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snapshotTasks_3057_);
lean_inc(v_infoState_3056_);
lean_inc(v_messages_3055_);
lean_inc(v_cache_3054_);
lean_inc(v_traceState_3053_);
lean_inc(v_auxDeclNGen_3052_);
lean_inc(v_ngen_3051_);
lean_inc(v_env_3050_);
lean_dec(v___x_3049_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3083_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v_macroScope_3044_);
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_env_3050_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_macroScope_3044_);
lean_ctor_set(v_reuseFailAlloc_3082_, 2, v_ngen_3051_);
lean_ctor_set(v_reuseFailAlloc_3082_, 3, v_auxDeclNGen_3052_);
lean_ctor_set(v_reuseFailAlloc_3082_, 4, v_traceState_3053_);
lean_ctor_set(v_reuseFailAlloc_3082_, 5, v_cache_3054_);
lean_ctor_set(v_reuseFailAlloc_3082_, 6, v_messages_3055_);
lean_ctor_set(v_reuseFailAlloc_3082_, 7, v_infoState_3056_);
lean_ctor_set(v_reuseFailAlloc_3082_, 8, v_snapshotTasks_3057_);
v___x_3062_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_st_ref_set(v___y_3018_, v___x_3062_);
v___x_3064_ = l_List_reverse___redArg(v_traceMsgs_3045_);
v___x_3065_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3064_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v___x_3065_, 0);
lean_dec(v_unused_3073_);
v___x_3067_ = v___x_3065_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_dec(v___x_3065_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 0, v_a_3043_);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3043_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_a_3043_);
v_a_3074_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3065_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3065_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_traceMsgs_3045_);
lean_dec(v_macroScope_3044_);
lean_dec(v_a_3043_);
v_a_3085_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3048_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3048_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; 
v_a_3093_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3041_, 2);
if (lean_obj_tag(v_a_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v_a_3094_ = lean_ctor_get(v_a_3093_, 0);
lean_inc(v_a_3094_);
v_a_3095_ = lean_ctor_get(v_a_3093_, 1);
lean_inc_ref(v_a_3095_);
lean_dec_ref_known(v_a_3093_, 2);
v___x_3096_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3097_ = lean_string_dec_eq(v_a_3095_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_a_3095_);
v___x_3099_ = l_Lean_MessageData_ofFormat(v___x_3098_);
v___x_3100_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3094_, v___x_3099_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v_a_3094_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; 
lean_dec_ref(v_a_3095_);
v___x_3101_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3094_);
return v___x_3101_;
}
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_quotContext_3117_; lean_object* v_currMacroScope_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_quotContext_3117_ = lean_ctor_get(v___y_3114_, 10);
lean_inc(v_quotContext_3117_);
v_currMacroScope_3118_ = lean_ctor_get(v___y_3114_, 11);
lean_inc(v_currMacroScope_3118_);
lean_dec_ref(v___y_3114_);
v___x_3119_ = l_Lean_addMacroScope(v_quotContext_3117_, v___x_3113_, v_currMacroScope_3118_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___f_3134_; lean_object* v___x_3135_; 
v___f_3134_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3135_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3134_, v___y_3131_, v___y_3132_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3140_, uint8_t v_canonical_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3159_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = l_Lean_mkIdentFrom(v_ref_3140_, v_a_3151_, v_canonical_3141_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3155_);
v___x_3157_ = v___x_3153_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3150_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3150_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3168_, lean_object* v_canonical_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v_canonical_boxed_3178_; lean_object* v_res_3179_; 
v_canonical_boxed_3178_ = lean_unbox(v_canonical_3169_);
v_res_3179_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3168_, v_canonical_boxed_3178_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v_ref_3168_);
return v_res_3179_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3192_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3193_ = l_Lean_Name_append(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3196_ = l_Lean_stringToMessageData(v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3199_ = l_Lean_stringToMessageData(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3203_, lean_object* v_letOrReassign_3204_, lean_object* v_decl_3205_, lean_object* v_tk_3206_, lean_object* v_dec_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3203_, v_letOrReassign_3204_, v_decl_3205_, v_tk_3206_, v_dec_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec_ref(v_a_3208_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3217_, lean_object* v_letOrReassign_3218_, lean_object* v_decl_3219_, lean_object* v_tk_3220_, lean_object* v_dec_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3217_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref_known(v___x_3230_, 1);
lean_inc(v_decl_3219_);
v___x_3231_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3219_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3218_, v_a_3232_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref_known(v___x_3233_, 1);
v___x_3234_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3221_, v_tk_3220_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3218_, v_decl_3219_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v_doBlockResultType_3238_; lean_object* v___x_3239_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v_doBlockResultType_3238_ = lean_ctor_get(v_a_3222_, 3);
lean_inc_ref(v_doBlockResultType_3238_);
v___x_3239_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3238_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3458_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3458_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3458_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v___x_3244_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3245_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3247_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3237_);
v___x_3248_ = l_Lean_Syntax_isOfKind(v_a_3237_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec(v_a_3237_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_tk_3220_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v___x_3249_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v___x_3250_ = lean_unsigned_to_nat(0u);
v___x_3251_ = l_Lean_Syntax_getArg(v_a_3237_, v___x_3250_);
lean_dec(v_a_3237_);
v___x_3252_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3251_);
v___x_3253_ = l_Lean_Syntax_isOfKind(v___x_3251_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
lean_dec(v_tk_3220_);
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3251_);
v___x_3255_ = l_Lean_Syntax_isOfKind(v___x_3251_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3251_);
v___x_3257_ = l_Lean_Syntax_isOfKind(v___x_3251_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
lean_dec(v___x_3251_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v___x_3258_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; lean_object* v_id_3260_; lean_object* v_binders_3261_; lean_object* v_type_3262_; lean_object* v_value_3263_; uint8_t v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; uint8_t v___y_3277_; lean_object* v_id_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___x_3354_; 
v___x_3259_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3251_);
lean_dec(v___x_3251_);
v_id_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_id_3260_);
v_binders_3261_ = lean_ctor_get(v___x_3259_, 1);
lean_inc_ref(v_binders_3261_);
v_type_3262_ = lean_ctor_get(v___x_3259_, 2);
lean_inc(v_type_3262_);
v_value_3263_ = lean_ctor_get(v___x_3259_, 3);
lean_inc(v_value_3263_);
lean_dec_ref(v___x_3259_);
v___x_3354_ = l_Lean_Syntax_isIdent(v_id_3260_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3260_, v___x_3248_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_id_3260_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref_known(v___x_3355_, 1);
v_id_3336_ = v_a_3356_;
v___y_3337_ = v_a_3222_;
v___y_3338_ = v_a_3223_;
v___y_3339_ = v_a_3224_;
v___y_3340_ = v_a_3225_;
v___y_3341_ = v_a_3226_;
v___y_3342_ = v_a_3227_;
v___y_3343_ = v_a_3228_;
goto v___jp_3335_;
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_value_3263_);
lean_dec(v_type_3262_);
lean_dec_ref(v_binders_3261_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3357_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3355_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
v_id_3336_ = v_id_3260_;
v___y_3337_ = v_a_3222_;
v___y_3338_ = v_a_3223_;
v___y_3339_ = v_a_3224_;
v___y_3340_ = v_a_3225_;
v___y_3341_ = v_a_3226_;
v___y_3342_ = v_a_3227_;
v___y_3343_ = v_a_3228_;
goto v___jp_3335_;
}
v___jp_3264_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; 
v___x_3278_ = lean_box(v___x_3248_);
v___x_3279_ = lean_box(v___x_3253_);
v___x_3280_ = lean_box(v___y_3277_);
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3281_, 0, v_type_3262_);
lean_closure_set(v___f_3281_, 1, v_value_3263_);
lean_closure_set(v___f_3281_, 2, v___x_3278_);
lean_closure_set(v___f_3281_, 3, v___x_3279_);
lean_closure_set(v___f_3281_, 4, v___x_3250_);
lean_closure_set(v___f_3281_, 5, v___x_3280_);
v___x_3282_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3261_, v___f_3281_, v___y_3269_, v___y_3271_, v___y_3270_, v___y_3273_, v___y_3272_, v___y_3276_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v_options_3284_; lean_object* v_fst_3285_; lean_object* v_snd_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3326_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v_options_3284_ = lean_ctor_get(v___y_3272_, 2);
v_fst_3285_ = lean_ctor_get(v_a_3283_, 0);
v_snd_3286_ = lean_ctor_get(v_a_3283_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_a_3283_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3288_ = v_a_3283_;
v_isShared_3289_ = v_isSharedCheck_3326_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_snd_3286_);
lean_inc(v_fst_3285_);
lean_dec(v_a_3283_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3326_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_inheritedTraceOptions_3290_; uint8_t v_hasTrace_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___f_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_inheritedTraceOptions_3290_ = lean_ctor_get(v___y_3272_, 13);
v_hasTrace_3291_ = lean_ctor_get_uint8(v_options_3284_, sizeof(void*)*1);
v___x_3292_ = lean_box(v___y_3268_);
v___x_3293_ = lean_box(v___y_3265_);
v___x_3294_ = lean_box(v___x_3253_);
v___x_3295_ = lean_box(v___y_3277_);
v___x_3296_ = lean_box(v___x_3248_);
lean_inc(v_snd_3286_);
v___f_3297_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3297_, 0, v___y_3267_);
lean_closure_set(v___f_3297_, 1, v___y_3266_);
lean_closure_set(v___f_3297_, 2, v_a_3235_);
lean_closure_set(v___f_3297_, 3, v___x_3292_);
lean_closure_set(v___f_3297_, 4, v___x_3293_);
lean_closure_set(v___f_3297_, 5, v___x_3294_);
lean_closure_set(v___f_3297_, 6, v_snd_3286_);
lean_closure_set(v___f_3297_, 7, v___x_3295_);
lean_closure_set(v___f_3297_, 8, v___x_3296_);
lean_closure_set(v___f_3297_, 9, v_letOrReassign_3218_);
lean_closure_set(v___f_3297_, 10, v_a_3232_);
v___x_3298_ = l_Lean_Syntax_getId(v___y_3275_);
lean_dec(v___y_3275_);
v___x_3299_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3298_);
if (v_hasTrace_3291_ == 0)
{
lean_object* v___x_3300_; 
lean_del_object(v___x_3288_);
v___x_3300_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3298_, v_fst_3285_, v_snd_3286_, v___f_3297_, v___y_3277_, v___x_3299_, v___y_3274_, v___y_3269_, v___y_3271_, v___y_3270_, v___y_3273_, v___y_3272_, v___y_3276_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3301_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3302_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3290_, v_options_3284_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; 
lean_del_object(v___x_3288_);
v___x_3304_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3298_, v_fst_3285_, v_snd_3286_, v___f_3297_, v___y_3277_, v___x_3299_, v___y_3274_, v___y_3269_, v___y_3271_, v___y_3270_, v___y_3273_, v___y_3272_, v___y_3276_);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_inc(v___x_3298_);
v___x_3305_ = l_Lean_MessageData_ofName(v___x_3298_);
v___x_3306_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 7);
lean_ctor_set(v___x_3288_, 1, v___x_3306_);
lean_ctor_set(v___x_3288_, 0, v___x_3305_);
v___x_3308_ = v___x_3288_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_inc(v_fst_3285_);
v___x_3309_ = l_Lean_MessageData_ofExpr(v_fst_3285_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_inc(v_snd_3286_);
v___x_3313_ = l_Lean_MessageData_ofExpr(v_snd_3286_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3301_, v___x_3314_, v___y_3270_, v___y_3273_, v___y_3272_, v___y_3276_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; 
lean_dec_ref_known(v___x_3315_, 1);
v___x_3316_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3298_, v_fst_3285_, v_snd_3286_, v___f_3297_, v___y_3277_, v___x_3299_, v___y_3274_, v___y_3269_, v___y_3271_, v___y_3270_, v___y_3273_, v___y_3272_, v___y_3276_);
return v___x_3316_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___x_3298_);
lean_dec_ref(v___f_3297_);
lean_dec(v_snd_3286_);
lean_dec(v_fst_3285_);
v_a_3317_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
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
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v___y_3275_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
v_a_3327_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3282_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3282_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
v___jp_3335_:
{
uint8_t v_nondep_3344_; 
v_nondep_3344_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1);
if (v_nondep_3344_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3218_) == 1)
{
uint8_t v_usedOnly_3345_; uint8_t v_zeta_3346_; lean_object* v_eq_x3f_3347_; 
v_usedOnly_3345_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 1);
v_zeta_3346_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 2);
v_eq_x3f_3347_ = lean_ctor_get(v_config_3217_, 0);
lean_inc(v_eq_x3f_3347_);
lean_dec_ref(v_config_3217_);
lean_inc(v_id_3336_);
v___y_3265_ = v_usedOnly_3345_;
v___y_3266_ = v_eq_x3f_3347_;
v___y_3267_ = v_id_3336_;
v___y_3268_ = v_zeta_3346_;
v___y_3269_ = v___y_3338_;
v___y_3270_ = v___y_3340_;
v___y_3271_ = v___y_3339_;
v___y_3272_ = v___y_3342_;
v___y_3273_ = v___y_3341_;
v___y_3274_ = v___y_3337_;
v___y_3275_ = v_id_3336_;
v___y_3276_ = v___y_3343_;
v___y_3277_ = v___x_3248_;
goto v___jp_3264_;
}
else
{
uint8_t v_usedOnly_3348_; uint8_t v_zeta_3349_; lean_object* v_eq_x3f_3350_; 
v_usedOnly_3348_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 1);
v_zeta_3349_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 2);
v_eq_x3f_3350_ = lean_ctor_get(v_config_3217_, 0);
lean_inc(v_eq_x3f_3350_);
lean_dec_ref(v_config_3217_);
lean_inc(v_id_3336_);
v___y_3265_ = v_usedOnly_3348_;
v___y_3266_ = v_eq_x3f_3350_;
v___y_3267_ = v_id_3336_;
v___y_3268_ = v_zeta_3349_;
v___y_3269_ = v___y_3338_;
v___y_3270_ = v___y_3340_;
v___y_3271_ = v___y_3339_;
v___y_3272_ = v___y_3342_;
v___y_3273_ = v___y_3341_;
v___y_3274_ = v___y_3337_;
v___y_3275_ = v_id_3336_;
v___y_3276_ = v___y_3343_;
v___y_3277_ = v_nondep_3344_;
goto v___jp_3264_;
}
}
else
{
uint8_t v_usedOnly_3351_; uint8_t v_zeta_3352_; lean_object* v_eq_x3f_3353_; 
v_usedOnly_3351_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 1);
v_zeta_3352_ = lean_ctor_get_uint8(v_config_3217_, sizeof(void*)*1 + 2);
v_eq_x3f_3353_ = lean_ctor_get(v_config_3217_, 0);
lean_inc(v_eq_x3f_3353_);
lean_dec_ref(v_config_3217_);
lean_inc(v_id_3336_);
v___y_3265_ = v_usedOnly_3351_;
v___y_3266_ = v_eq_x3f_3353_;
v___y_3267_ = v_id_3336_;
v___y_3268_ = v_zeta_3352_;
v___y_3269_ = v___y_3338_;
v___y_3270_ = v___y_3340_;
v___y_3271_ = v___y_3339_;
v___y_3272_ = v___y_3342_;
v___y_3273_ = v___y_3341_;
v___y_3274_ = v___y_3337_;
v___y_3275_ = v_id_3336_;
v___y_3276_ = v___y_3343_;
v___y_3277_ = v___x_3248_;
goto v___jp_3264_;
}
}
}
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = l_Lean_Syntax_getArg(v___x_3251_, v___x_3365_);
v___x_3367_ = l_Lean_Syntax_matchesNull(v___x_3366_, v___x_3250_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_dec(v___x_3251_);
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v___x_3368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3368_;
}
else
{
lean_object* v___x_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v_rhs_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v_xType_x3f_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3369_ = lean_box(v___x_3253_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3370_, 0, v___x_3369_);
v___x_3371_ = l_Lean_Syntax_getArg(v___x_3251_, v___x_3250_);
v___x_3426_ = lean_unsigned_to_nat(2u);
v___x_3427_ = l_Lean_Syntax_getArg(v___x_3251_, v___x_3426_);
v___x_3428_ = l_Lean_Syntax_isNone(v___x_3427_);
if (v___x_3428_ == 0)
{
uint8_t v___x_3429_; 
lean_inc(v___x_3427_);
v___x_3429_ = l_Lean_Syntax_matchesNull(v___x_3427_, v___x_3365_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v___x_3427_);
lean_dec(v___x_3371_);
lean_dec_ref(v___f_3370_);
lean_dec(v___x_3251_);
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v___x_3430_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = l_Lean_Syntax_getArg(v___x_3427_, v___x_3250_);
lean_dec(v___x_3427_);
v___x_3432_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3431_);
v___x_3433_ = l_Lean_Syntax_isOfKind(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_dec(v___x_3431_);
lean_dec(v___x_3371_);
lean_dec_ref(v___f_3370_);
lean_dec(v___x_3251_);
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v___x_3434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_Syntax_getArg(v___x_3431_, v___x_3365_);
lean_dec(v___x_3431_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 1);
lean_ctor_set(v___x_3242_, 0, v___x_3435_);
v___x_3437_ = v___x_3242_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
v_xType_x3f_3392_ = v___x_3437_;
v___y_3393_ = v_a_3222_;
v___y_3394_ = v_a_3223_;
v___y_3395_ = v_a_3224_;
v___y_3396_ = v_a_3225_;
v___y_3397_ = v_a_3226_;
v___y_3398_ = v_a_3227_;
v___y_3399_ = v_a_3228_;
goto v___jp_3391_;
}
}
}
}
else
{
lean_object* v___x_3439_; 
lean_dec(v___x_3427_);
lean_del_object(v___x_3242_);
v___x_3439_ = lean_box(0);
v_xType_x3f_3392_ = v___x_3439_;
v___y_3393_ = v_a_3222_;
v___y_3394_ = v_a_3223_;
v___y_3395_ = v_a_3224_;
v___y_3396_ = v_a_3225_;
v___y_3397_ = v_a_3226_;
v___y_3398_ = v_a_3227_;
v___y_3399_ = v_a_3228_;
goto v___jp_3391_;
}
v___jp_3372_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3381_ = lean_box(v___x_3253_);
v___x_3382_ = lean_box(v___x_3248_);
lean_inc(v___x_3371_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3383_, 0, v_rhs_3373_);
lean_closure_set(v___f_3383_, 1, v___x_3381_);
lean_closure_set(v___f_3383_, 2, v_config_3217_);
lean_closure_set(v___f_3383_, 3, v_a_3240_);
lean_closure_set(v___f_3383_, 4, v___x_3382_);
lean_closure_set(v___f_3383_, 5, v___x_3244_);
lean_closure_set(v___f_3383_, 6, v___x_3245_);
lean_closure_set(v___f_3383_, 7, v___x_3246_);
lean_closure_set(v___f_3383_, 8, v___f_3370_);
lean_closure_set(v___f_3383_, 9, v___x_3371_);
v___x_3384_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3384_, 0, v_a_3235_);
v___x_3385_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3385_, 0, v_letOrReassign_3218_);
lean_closure_set(v___x_3385_, 1, v_a_3232_);
lean_closure_set(v___x_3385_, 2, v___x_3384_);
v___x_3386_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3387_ = l_Lean_MessageData_ofSyntax(v___x_3371_);
v___x_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_box(0);
v___x_3390_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3388_, v___x_3385_, v___f_3383_, v___x_3389_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
return v___x_3390_;
}
v___jp_3391_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_unsigned_to_nat(4u);
v___x_3401_ = l_Lean_Syntax_getArg(v___x_3251_, v___x_3400_);
lean_dec(v___x_3251_);
if (lean_obj_tag(v_xType_x3f_3392_) == 0)
{
v_rhs_3373_ = v___x_3401_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3394_;
v___y_3376_ = v___y_3395_;
v___y_3377_ = v___y_3396_;
v___y_3378_ = v___y_3397_;
v___y_3379_ = v___y_3398_;
v___y_3380_ = v___y_3399_;
goto v___jp_3372_;
}
else
{
lean_object* v_val_3402_; lean_object* v_ref_3403_; lean_object* v_quotContext_3404_; lean_object* v_currMacroScope_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_val_3402_ = lean_ctor_get(v_xType_x3f_3392_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v_xType_x3f_3392_, 1);
v_ref_3403_ = lean_ctor_get(v___y_3398_, 5);
v_quotContext_3404_ = lean_ctor_get(v___y_3398_, 10);
v_currMacroScope_3405_ = lean_ctor_get(v___y_3398_, 11);
v___x_3406_ = l_Lean_SourceInfo_fromRef(v_ref_3403_, v___x_3253_);
v___x_3407_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3408_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3406_, 7);
v___x_3410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3406_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3412_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3413_ = lean_box(0);
lean_inc(v_currMacroScope_3405_);
lean_inc(v_quotContext_3404_);
v___x_3414_ = l_Lean_addMacroScope(v_quotContext_3404_, v___x_3413_, v_currMacroScope_3405_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3406_);
lean_ctor_set(v___x_3416_, 1, v___x_3412_);
lean_ctor_set(v___x_3416_, 2, v___x_3414_);
lean_ctor_set(v___x_3416_, 3, v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node1(v___x_3406_, v___x_3411_, v___x_3416_);
v___x_3418_ = l_Lean_Syntax_node2(v___x_3406_, v___x_3408_, v___x_3410_, v___x_3417_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3406_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3422_ = l_Lean_Syntax_node1(v___x_3406_, v___x_3421_, v_val_3402_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3406_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_Syntax_node5(v___x_3406_, v___x_3407_, v___x_3418_, v___x_3401_, v___x_3420_, v___x_3422_, v___x_3424_);
v_rhs_3373_ = v___x_3425_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3394_;
v___y_3376_ = v___y_3395_;
v___y_3377_ = v___y_3396_;
v___y_3378_ = v___y_3397_;
v___y_3379_ = v___y_3398_;
v___y_3380_ = v___y_3399_;
goto v___jp_3372_;
}
}
}
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_del_object(v___x_3242_);
lean_dec(v_a_3240_);
lean_dec(v_a_3232_);
v___x_3440_ = lean_box(v___x_3248_);
lean_inc(v___x_3251_);
v___x_3441_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3441_, 0, v___x_3251_);
lean_closure_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3441_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v_ref_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v_ref_3444_ = lean_ctor_get(v_a_3227_, 5);
v___x_3445_ = 0;
v___x_3446_ = l_Lean_SourceInfo_fromRef(v_ref_3444_, v___x_3445_);
v___x_3447_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3247_, v_a_3443_);
lean_inc(v___x_3447_);
v___x_3448_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3448_, 0, v_config_3217_);
lean_closure_set(v___x_3448_, 1, v_letOrReassign_3218_);
lean_closure_set(v___x_3448_, 2, v___x_3447_);
lean_closure_set(v___x_3448_, 3, v_tk_3220_);
lean_closure_set(v___x_3448_, 4, v_a_3235_);
v___x_3449_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3251_, v___x_3447_, v___x_3448_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v___x_3251_);
lean_dec(v_a_3235_);
lean_dec(v_tk_3220_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3450_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3442_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3442_);
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
}
}
}
else
{
lean_dec(v_a_3237_);
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_tk_3220_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
return v___x_3239_;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_a_3235_);
lean_dec(v_a_3232_);
lean_dec(v_tk_3220_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3459_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3236_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3236_);
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
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_a_3232_);
lean_dec(v_tk_3220_);
lean_dec(v_decl_3219_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3467_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3234_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3234_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_a_3232_);
lean_dec_ref(v_dec_3221_);
lean_dec(v_tk_3220_);
lean_dec(v_decl_3219_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3475_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3233_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3233_);
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
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_dec_3221_);
lean_dec(v_tk_3220_);
lean_dec(v_decl_3219_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3483_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3231_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3231_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_dec_3221_);
lean_dec(v_tk_3220_);
lean_dec(v_decl_3219_);
lean_dec(v_letOrReassign_3218_);
lean_dec_ref(v_config_3217_);
v_a_3491_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3230_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3230_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3499_, lean_object* v_x_3500_, lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3500_, v_x_3501_, v_x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3504_, lean_object* v_msg_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3504_, v_msg_3505_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3515_, lean_object* v_msg_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3515_, v_msg_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3531_, v___y_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3544_, lean_object* v_beforeStx_3545_, lean_object* v_afterStx_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3545_, v_afterStx_3546_, v_x_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3557_, lean_object* v_beforeStx_3558_, lean_object* v_afterStx_3559_, lean_object* v_x_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3557_, v_beforeStx_3558_, v_afterStx_3559_, v_x_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v___y_3561_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3571_, v___y_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3575_, lean_object* v_x_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3575_, v_x_3576_, v___y_3577_, v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_x_3576_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3580_, lean_object* v_ref_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3581_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_ref_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3591_, v_ref_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_x_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3613_, v_x_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3624_, lean_object* v_x_3625_, size_t v_x_3626_, size_t v_x_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3625_, v_x_3626_, v_x_3627_, v_x_3628_, v_x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
size_t v_x_102764__boxed_3637_; size_t v_x_102765__boxed_3638_; lean_object* v_res_3639_; 
v_x_102764__boxed_3637_ = lean_unbox_usize(v_x_3633_);
lean_dec(v_x_3633_);
v_x_102765__boxed_3638_ = lean_unbox_usize(v_x_3634_);
lean_dec(v_x_3634_);
v_res_3639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3631_, v_x_3632_, v_x_102764__boxed_3637_, v_x_102765__boxed_3638_, v_x_3635_, v_x_3636_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3640_, lean_object* v_stx_3641_, lean_object* v_output_3642_, lean_object* v_x_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3641_, v_output_3642_, v_x_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_stx_3653_, lean_object* v_output_3654_, lean_object* v_x_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3652_, v_stx_3653_, v_output_3654_, v_x_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3664_, lean_object* v_as_x27_3665_, lean_object* v_b_3666_, lean_object* v_a_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3665_, v_b_3666_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3677_, lean_object* v_as_x27_3678_, lean_object* v_b_3679_, lean_object* v_a_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3677_, v_as_x27_3678_, v_b_3679_, v_a_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v_as_x27_3678_);
lean_dec(v_as_3677_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3690_, lean_object* v_ref_3691_, lean_object* v_msg_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3691_, v_msg_3692_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_ref_3703_, lean_object* v_msg_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3702_, v_ref_3703_, v_msg_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v_ref_3703_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3714_, lean_object* v_n_3715_, lean_object* v_k_3716_, lean_object* v_v_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3715_, v_k_3716_, v_v_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3719_, size_t v_depth_3720_, lean_object* v_keys_3721_, lean_object* v_vals_3722_, lean_object* v_heq_3723_, lean_object* v_i_3724_, lean_object* v_entries_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3720_, v_keys_3721_, v_vals_3722_, v_i_3724_, v_entries_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3727_, lean_object* v_depth_3728_, lean_object* v_keys_3729_, lean_object* v_vals_3730_, lean_object* v_heq_3731_, lean_object* v_i_3732_, lean_object* v_entries_3733_){
_start:
{
size_t v_depth_boxed_3734_; lean_object* v_res_3735_; 
v_depth_boxed_3734_ = lean_unbox_usize(v_depth_3728_);
lean_dec(v_depth_3728_);
v_res_3735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3727_, v_depth_boxed_3734_, v_keys_3729_, v_vals_3730_, v_heq_3731_, v_i_3732_, v_entries_3733_);
lean_dec_ref(v_vals_3730_);
lean_dec_ref(v_keys_3729_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3752_, lean_object* v_x_3753_, lean_object* v_mkInfoTree_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3753_, v_mkInfoTree_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_x_3764_, lean_object* v_mkInfoTree_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3763_, v_x_3764_, v_mkInfoTree_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3774_, lean_object* v_m_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3775_, v_a_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3778_, lean_object* v_m_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3778_, v_m_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_m_3779_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3783_, v_x_3784_, v_x_3785_, v_x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3788_, lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
uint8_t v___x_3791_; 
v___x_3791_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3789_, v_x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3792_, lean_object* v_x_3793_, lean_object* v_x_3794_){
_start:
{
uint8_t v_res_3795_; lean_object* v_r_3796_; 
v_res_3795_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3792_, v_x_3793_, v_x_3794_);
lean_dec_ref(v_x_3794_);
lean_dec_ref(v_x_3793_);
v_r_3796_ = lean_box(v_res_3795_);
return v_r_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3797_, lean_object* v_a_3798_, lean_object* v_x_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_3798_, v_x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3801_, lean_object* v_a_3802_, lean_object* v_x_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3801_, v_a_3802_, v_x_3803_);
lean_dec(v_x_3803_);
lean_dec(v_a_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3805_, lean_object* v_x_3806_, size_t v_x_3807_, lean_object* v_x_3808_){
_start:
{
uint8_t v___x_3809_; 
v___x_3809_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3806_, v_x_3807_, v_x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3810_, lean_object* v_x_3811_, lean_object* v_x_3812_, lean_object* v_x_3813_){
_start:
{
size_t v_x_102934__boxed_3814_; uint8_t v_res_3815_; lean_object* v_r_3816_; 
v_x_102934__boxed_3814_ = lean_unbox_usize(v_x_3812_);
lean_dec(v_x_3812_);
v_res_3815_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3810_, v_x_3811_, v_x_102934__boxed_3814_, v_x_3813_);
lean_dec_ref(v_x_3813_);
lean_dec_ref(v_x_3811_);
v_r_3816_ = lean_box(v_res_3815_);
return v_r_3816_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3817_, lean_object* v_keys_3818_, lean_object* v_vals_3819_, lean_object* v_heq_3820_, lean_object* v_i_3821_, lean_object* v_k_3822_){
_start:
{
uint8_t v___x_3823_; 
v___x_3823_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3818_, v_i_3821_, v_k_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3824_, lean_object* v_keys_3825_, lean_object* v_vals_3826_, lean_object* v_heq_3827_, lean_object* v_i_3828_, lean_object* v_k_3829_){
_start:
{
uint8_t v_res_3830_; lean_object* v_r_3831_; 
v_res_3830_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3824_, v_keys_3825_, v_vals_3826_, v_heq_3827_, v_i_3828_, v_k_3829_);
lean_dec_ref(v_k_3829_);
lean_dec_ref(v_vals_3826_);
lean_dec_ref(v_keys_3825_);
v_r_3831_ = lean_box(v_res_3830_);
return v_r_3831_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3835_ = l_Lean_stringToMessageData(v___x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3841_, lean_object* v_otherwise_x3f_3842_, uint8_t v___x_3843_, lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v_dec_3849_, uint8_t v___x_3850_, lean_object* v___y_3851_, lean_object* v___x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; uint8_t v___y_3884_; 
switch(lean_obj_tag(v_letOrReassign_3841_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3842_) == 1)
{
lean_object* v_mutTk_x3f_3895_; lean_object* v_val_3896_; lean_object* v_ref_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3927_; 
v_mutTk_x3f_3895_ = lean_ctor_get(v_letOrReassign_3841_, 0);
v_val_3896_ = lean_ctor_get(v_otherwise_x3f_3842_, 0);
lean_inc(v_val_3896_);
lean_dec_ref_known(v_otherwise_x3f_3842_, 1);
v_ref_3897_ = lean_ctor_get(v___y_3858_, 5);
v___x_3898_ = l_Lean_SourceInfo_fromRef(v_ref_3897_, v___x_3843_);
v___x_3899_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3846_);
lean_inc_ref(v___x_3845_);
lean_inc_ref(v___x_3844_);
v___x_3900_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3899_);
v___x_3901_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3898_);
v___x_3902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3898_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3904_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3895_) == 1)
{
lean_object* v_val_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_val_3942_ = lean_ctor_get(v_mutTk_x3f_3895_, 0);
v___x_3943_ = l_Lean_SourceInfo_fromRef(v_val_3942_, v___x_3850_);
v___x_3944_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Array_mkArray1___redArg(v___x_3945_);
v___y_3927_ = v___x_3946_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_mk_empty_array_with_capacity(v___x_3852_);
v___y_3927_ = v___x_3947_;
goto v___jp_3926_;
}
v___jp_3905_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3911_ = l_Array_append___redArg(v___x_3904_, v___y_3910_);
lean_dec_ref(v___y_3910_);
lean_inc(v___x_3898_);
v___x_3912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3898_);
lean_ctor_set(v___x_3912_, 1, v___x_3903_);
lean_ctor_set(v___x_3912_, 2, v___x_3911_);
v___x_3913_ = lean_unsigned_to_nat(9u);
v___x_3914_ = lean_mk_empty_array_with_capacity(v___x_3913_);
v___x_3915_ = lean_array_push(v___x_3914_, v___x_3902_);
v___x_3916_ = lean_array_push(v___x_3915_, v___y_3909_);
v___x_3917_ = lean_array_push(v___x_3916_, v___y_3908_);
v___x_3918_ = lean_array_push(v___x_3917_, v___x_3847_);
v___x_3919_ = lean_array_push(v___x_3918_, v___y_3906_);
v___x_3920_ = lean_array_push(v___x_3919_, v___x_3848_);
v___x_3921_ = lean_array_push(v___x_3920_, v___y_3907_);
v___x_3922_ = lean_array_push(v___x_3921_, v_val_3896_);
v___x_3923_ = lean_array_push(v___x_3922_, v___x_3912_);
v___x_3924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3898_);
lean_ctor_set(v___x_3924_, 1, v___x_3900_);
lean_ctor_set(v___x_3924_, 2, v___x_3923_);
v___x_3925_ = l_Lean_Elab_Do_elabDoElem(v___x_3924_, v_dec_3849_, v___x_3850_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3925_;
}
v___jp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3928_ = l_Array_append___redArg(v___x_3904_, v___y_3927_);
lean_dec_ref(v___y_3927_);
lean_inc_n(v___x_3898_, 5);
v___x_3929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3898_);
lean_ctor_set(v___x_3929_, 1, v___x_3903_);
lean_ctor_set(v___x_3929_, 2, v___x_3928_);
v___x_3930_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3931_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3898_);
lean_ctor_set(v___x_3932_, 1, v___x_3903_);
lean_ctor_set(v___x_3932_, 2, v___x_3904_);
v___x_3933_ = l_Lean_Syntax_node1(v___x_3898_, v___x_3931_, v___x_3932_);
v___x_3934_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3898_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_3937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3898_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
if (lean_obj_tag(v___y_3851_) == 0)
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_mk_empty_array_with_capacity(v___x_3852_);
v___y_3906_ = v___x_3935_;
v___y_3907_ = v___x_3937_;
v___y_3908_ = v___x_3933_;
v___y_3909_ = v___x_3929_;
v___y_3910_ = v___x_3938_;
goto v___jp_3905_;
}
else
{
lean_object* v_val_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_val_3939_ = lean_ctor_get(v___y_3851_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v___y_3851_, 1);
v___x_3940_ = lean_mk_empty_array_with_capacity(v___x_3852_);
v___x_3941_ = lean_array_push(v___x_3940_, v_val_3939_);
v___y_3906_ = v___x_3935_;
v___y_3907_ = v___x_3937_;
v___y_3908_ = v___x_3933_;
v___y_3909_ = v___x_3929_;
v___y_3910_ = v___x_3941_;
goto v___jp_3905_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3948_; lean_object* v_ref_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___y_3958_; 
lean_dec(v___y_3851_);
lean_dec(v_otherwise_x3f_3842_);
v_mutTk_x3f_3948_ = lean_ctor_get(v_letOrReassign_3841_, 0);
v_ref_3949_ = lean_ctor_get(v___y_3858_, 5);
v___x_3950_ = l_Lean_SourceInfo_fromRef(v_ref_3949_, v___x_3843_);
v___x_3951_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3846_);
lean_inc_ref(v___x_3845_);
lean_inc_ref(v___x_3844_);
v___x_3952_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3951_);
v___x_3953_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3950_);
v___x_3954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3950_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3956_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3948_) == 1)
{
lean_object* v_val_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_val_3975_ = lean_ctor_get(v_mutTk_x3f_3948_, 0);
v___x_3976_ = l_Lean_SourceInfo_fromRef(v_val_3975_, v___x_3850_);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = l_Array_mkArray1___redArg(v___x_3978_);
v___y_3958_ = v___x_3979_;
goto v___jp_3957_;
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_mk_empty_array_with_capacity(v___x_3852_);
v___y_3958_ = v___x_3980_;
goto v___jp_3957_;
}
v___jp_3957_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3959_ = l_Array_append___redArg(v___x_3956_, v___y_3958_);
lean_dec_ref(v___y_3958_);
lean_inc_n(v___x_3950_, 6);
v___x_3960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3950_);
lean_ctor_set(v___x_3960_, 1, v___x_3955_);
lean_ctor_set(v___x_3960_, 2, v___x_3959_);
v___x_3961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3846_, 2);
lean_inc_ref_n(v___x_3845_, 2);
lean_inc_ref_n(v___x_3844_, 2);
v___x_3962_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3950_);
lean_ctor_set(v___x_3963_, 1, v___x_3955_);
lean_ctor_set(v___x_3963_, 2, v___x_3956_);
lean_inc_ref_n(v___x_3963_, 2);
v___x_3964_ = l_Lean_Syntax_node1(v___x_3950_, v___x_3962_, v___x_3963_);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3966_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3968_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3967_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3950_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l_Lean_Syntax_node5(v___x_3950_, v___x_3968_, v___x_3847_, v___x_3963_, v___x_3963_, v___x_3970_, v___x_3848_);
v___x_3972_ = l_Lean_Syntax_node1(v___x_3950_, v___x_3966_, v___x_3971_);
v___x_3973_ = l_Lean_Syntax_node4(v___x_3950_, v___x_3952_, v___x_3954_, v___x_3960_, v___x_3964_, v___x_3972_);
v___x_3974_ = l_Lean_Elab_Do_elabDoElem(v___x_3973_, v_dec_3849_, v___x_3850_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3974_;
}
}
}
case 1:
{
lean_dec(v___y_3851_);
if (lean_obj_tag(v_otherwise_x3f_3842_) == 1)
{
lean_object* v___x_3981_; 
lean_dec_ref_known(v_otherwise_x3f_3842_, 1);
lean_dec_ref(v_dec_3849_);
lean_dec(v___x_3848_);
lean_dec(v___x_3847_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v___x_3844_);
v___x_3981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3981_;
}
else
{
lean_object* v_ref_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec(v_otherwise_x3f_3842_);
v_ref_3982_ = lean_ctor_get(v___y_3858_, 5);
v___x_3983_ = l_Lean_SourceInfo_fromRef(v_ref_3982_, v___x_3843_);
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3846_, 3);
lean_inc_ref_n(v___x_3845_, 3);
lean_inc_ref_n(v___x_3844_, 3);
v___x_3985_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3984_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3983_, 6);
v___x_3987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3983_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3989_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3988_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3991_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3983_);
lean_ctor_set(v___x_3992_, 1, v___x_3990_);
lean_ctor_set(v___x_3992_, 2, v___x_3991_);
lean_inc_ref_n(v___x_3992_, 2);
v___x_3993_ = l_Lean_Syntax_node1(v___x_3983_, v___x_3989_, v___x_3992_);
v___x_3994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3995_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3994_);
v___x_3996_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3997_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3996_);
v___x_3998_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3983_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = l_Lean_Syntax_node5(v___x_3983_, v___x_3997_, v___x_3847_, v___x_3992_, v___x_3992_, v___x_3999_, v___x_3848_);
v___x_4001_ = l_Lean_Syntax_node1(v___x_3983_, v___x_3995_, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node3(v___x_3983_, v___x_3985_, v___x_3987_, v___x_3993_, v___x_4001_);
v___x_4003_ = l_Lean_Elab_Do_elabDoElem(v___x_4002_, v_dec_3849_, v___x_3850_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_4003_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3842_);
if (lean_obj_tag(v___y_3851_) == 0)
{
v___y_3884_ = v___x_3850_;
goto v___jp_3883_;
}
else
{
lean_dec_ref_known(v___y_3851_, 1);
v___y_3884_ = v___x_3843_;
goto v___jp_3883_;
}
}
}
v___jp_3861_:
{
lean_object* v_ref_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_ref_3869_ = lean_ctor_get(v___y_3867_, 5);
v___x_3870_ = l_Lean_SourceInfo_fromRef(v_ref_3869_, v___x_3843_);
v___x_3871_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3846_);
lean_inc_ref(v___x_3845_);
lean_inc_ref(v___x_3844_);
v___x_3872_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3871_);
v___x_3873_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3874_ = l_Lean_Name_mkStr4(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3873_);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3876_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3870_, 3);
v___x_3877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3870_);
lean_ctor_set(v___x_3877_, 1, v___x_3875_);
lean_ctor_set(v___x_3877_, 2, v___x_3876_);
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3870_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
lean_inc_ref(v___x_3877_);
v___x_3880_ = l_Lean_Syntax_node5(v___x_3870_, v___x_3874_, v___x_3847_, v___x_3877_, v___x_3877_, v___x_3879_, v___x_3848_);
v___x_3881_ = l_Lean_Syntax_node1(v___x_3870_, v___x_3872_, v___x_3880_);
v___x_3882_ = l_Lean_Elab_Do_elabDoElem(v___x_3881_, v_dec_3849_, v___x_3850_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3882_;
}
v___jp_3883_:
{
if (v___y_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_dec_3849_);
lean_dec(v___x_3848_);
lean_dec(v___x_3847_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3845_);
lean_dec_ref(v___x_3844_);
v___x_3885_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3886_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_3885_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
else
{
v___y_3862_ = v___y_3853_;
v___y_3863_ = v___y_3854_;
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
goto v___jp_3861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4004_ = _args[0];
lean_object* v_otherwise_x3f_4005_ = _args[1];
lean_object* v___x_4006_ = _args[2];
lean_object* v___x_4007_ = _args[3];
lean_object* v___x_4008_ = _args[4];
lean_object* v___x_4009_ = _args[5];
lean_object* v___x_4010_ = _args[6];
lean_object* v___x_4011_ = _args[7];
lean_object* v_dec_4012_ = _args[8];
lean_object* v___x_4013_ = _args[9];
lean_object* v___y_4014_ = _args[10];
lean_object* v___x_4015_ = _args[11];
lean_object* v___y_4016_ = _args[12];
lean_object* v___y_4017_ = _args[13];
lean_object* v___y_4018_ = _args[14];
lean_object* v___y_4019_ = _args[15];
lean_object* v___y_4020_ = _args[16];
lean_object* v___y_4021_ = _args[17];
lean_object* v___y_4022_ = _args[18];
lean_object* v___y_4023_ = _args[19];
_start:
{
uint8_t v___x_39001__boxed_4024_; uint8_t v___x_39007__boxed_4025_; lean_object* v_res_4026_; 
v___x_39001__boxed_4024_ = lean_unbox(v___x_4006_);
v___x_39007__boxed_4025_ = lean_unbox(v___x_4013_);
v_res_4026_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4004_, v_otherwise_x3f_4005_, v___x_39001__boxed_4024_, v___x_4007_, v___x_4008_, v___x_4009_, v___x_4010_, v___x_4011_, v_dec_4012_, v___x_39007__boxed_4025_, v___y_4014_, v___x_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___x_4015_);
lean_dec(v_letOrReassign_4004_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4027_, lean_object* v_otherwise_x3f_4028_, uint8_t v___x_4029_, lean_object* v___x_4030_, lean_object* v___x_4031_, lean_object* v___x_4032_, lean_object* v___x_4033_, lean_object* v___x_4034_, lean_object* v_dec_4035_, uint8_t v___x_4036_, lean_object* v___y_4037_, lean_object* v___x_4038_, uint8_t v___x_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; uint8_t v___y_4071_; 
switch(lean_obj_tag(v_letOrReassign_4027_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4028_) == 1)
{
lean_object* v_mutTk_x3f_4082_; lean_object* v_val_4083_; lean_object* v_ref_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4114_; 
v_mutTk_x3f_4082_ = lean_ctor_get(v_letOrReassign_4027_, 0);
v_val_4083_ = lean_ctor_get(v_otherwise_x3f_4028_, 0);
lean_inc(v_val_4083_);
lean_dec_ref_known(v_otherwise_x3f_4028_, 1);
v_ref_4084_ = lean_ctor_get(v___y_4045_, 5);
v___x_4085_ = l_Lean_SourceInfo_fromRef(v_ref_4084_, v___x_4029_);
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4032_);
lean_inc_ref(v___x_4031_);
lean_inc_ref(v___x_4030_);
v___x_4087_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4086_);
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4085_);
v___x_4089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4085_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4091_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4082_) == 1)
{
lean_object* v_val_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_val_4129_ = lean_ctor_get(v_mutTk_x3f_4082_, 0);
v___x_4130_ = l_Lean_SourceInfo_fromRef(v_val_4129_, v___x_4036_);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4130_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Array_mkArray1___redArg(v___x_4132_);
v___y_4114_ = v___x_4133_;
goto v___jp_4113_;
}
else
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_mk_empty_array_with_capacity(v___x_4038_);
v___y_4114_ = v___x_4134_;
goto v___jp_4113_;
}
v___jp_4092_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4098_ = l_Array_append___redArg(v___x_4091_, v___y_4097_);
lean_dec_ref(v___y_4097_);
lean_inc(v___x_4085_);
v___x_4099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4085_);
lean_ctor_set(v___x_4099_, 1, v___x_4090_);
lean_ctor_set(v___x_4099_, 2, v___x_4098_);
v___x_4100_ = lean_unsigned_to_nat(9u);
v___x_4101_ = lean_mk_empty_array_with_capacity(v___x_4100_);
v___x_4102_ = lean_array_push(v___x_4101_, v___x_4089_);
v___x_4103_ = lean_array_push(v___x_4102_, v___y_4095_);
v___x_4104_ = lean_array_push(v___x_4103_, v___y_4096_);
v___x_4105_ = lean_array_push(v___x_4104_, v___x_4033_);
v___x_4106_ = lean_array_push(v___x_4105_, v___y_4093_);
v___x_4107_ = lean_array_push(v___x_4106_, v___x_4034_);
v___x_4108_ = lean_array_push(v___x_4107_, v___y_4094_);
v___x_4109_ = lean_array_push(v___x_4108_, v_val_4083_);
v___x_4110_ = lean_array_push(v___x_4109_, v___x_4099_);
v___x_4111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4085_);
lean_ctor_set(v___x_4111_, 1, v___x_4087_);
lean_ctor_set(v___x_4111_, 2, v___x_4110_);
v___x_4112_ = l_Lean_Elab_Do_elabDoElem(v___x_4111_, v_dec_4035_, v___x_4036_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4112_;
}
v___jp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4115_ = l_Array_append___redArg(v___x_4091_, v___y_4114_);
lean_dec_ref(v___y_4114_);
lean_inc_n(v___x_4085_, 5);
v___x_4116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4085_);
lean_ctor_set(v___x_4116_, 1, v___x_4090_);
lean_ctor_set(v___x_4116_, 2, v___x_4115_);
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4118_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4117_);
v___x_4119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4085_);
lean_ctor_set(v___x_4119_, 1, v___x_4090_);
lean_ctor_set(v___x_4119_, 2, v___x_4091_);
v___x_4120_ = l_Lean_Syntax_node1(v___x_4085_, v___x_4118_, v___x_4119_);
v___x_4121_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4085_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4085_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
if (lean_obj_tag(v___y_4037_) == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_mk_empty_array_with_capacity(v___x_4038_);
v___y_4093_ = v___x_4122_;
v___y_4094_ = v___x_4124_;
v___y_4095_ = v___x_4116_;
v___y_4096_ = v___x_4120_;
v___y_4097_ = v___x_4125_;
goto v___jp_4092_;
}
else
{
lean_object* v_val_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_val_4126_ = lean_ctor_get(v___y_4037_, 0);
lean_inc(v_val_4126_);
lean_dec_ref_known(v___y_4037_, 1);
v___x_4127_ = lean_mk_empty_array_with_capacity(v___x_4038_);
v___x_4128_ = lean_array_push(v___x_4127_, v_val_4126_);
v___y_4093_ = v___x_4122_;
v___y_4094_ = v___x_4124_;
v___y_4095_ = v___x_4116_;
v___y_4096_ = v___x_4120_;
v___y_4097_ = v___x_4128_;
goto v___jp_4092_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4135_; lean_object* v_ref_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___y_4145_; 
lean_dec(v___y_4037_);
lean_dec(v_otherwise_x3f_4028_);
v_mutTk_x3f_4135_ = lean_ctor_get(v_letOrReassign_4027_, 0);
v_ref_4136_ = lean_ctor_get(v___y_4045_, 5);
v___x_4137_ = l_Lean_SourceInfo_fromRef(v_ref_4136_, v___x_4029_);
v___x_4138_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4032_);
lean_inc_ref(v___x_4031_);
lean_inc_ref(v___x_4030_);
v___x_4139_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4138_);
v___x_4140_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4137_);
v___x_4141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4137_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4143_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4135_) == 1)
{
lean_object* v_val_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_val_4162_ = lean_ctor_get(v_mutTk_x3f_4135_, 0);
v___x_4163_ = l_Lean_SourceInfo_fromRef(v_val_4162_, v___x_4036_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l_Array_mkArray1___redArg(v___x_4165_);
v___y_4145_ = v___x_4166_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_mk_empty_array_with_capacity(v___x_4038_);
v___y_4145_ = v___x_4167_;
goto v___jp_4144_;
}
v___jp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4146_ = l_Array_append___redArg(v___x_4143_, v___y_4145_);
lean_dec_ref(v___y_4145_);
lean_inc_n(v___x_4137_, 6);
v___x_4147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4137_);
lean_ctor_set(v___x_4147_, 1, v___x_4142_);
lean_ctor_set(v___x_4147_, 2, v___x_4146_);
v___x_4148_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4032_, 2);
lean_inc_ref_n(v___x_4031_, 2);
lean_inc_ref_n(v___x_4030_, 2);
v___x_4149_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4137_);
lean_ctor_set(v___x_4150_, 1, v___x_4142_);
lean_ctor_set(v___x_4150_, 2, v___x_4143_);
lean_inc_ref_n(v___x_4150_, 2);
v___x_4151_ = l_Lean_Syntax_node1(v___x_4137_, v___x_4149_, v___x_4150_);
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4153_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4155_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4154_);
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4137_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_Syntax_node5(v___x_4137_, v___x_4155_, v___x_4033_, v___x_4150_, v___x_4150_, v___x_4157_, v___x_4034_);
v___x_4159_ = l_Lean_Syntax_node1(v___x_4137_, v___x_4153_, v___x_4158_);
v___x_4160_ = l_Lean_Syntax_node4(v___x_4137_, v___x_4139_, v___x_4141_, v___x_4147_, v___x_4151_, v___x_4159_);
v___x_4161_ = l_Lean_Elab_Do_elabDoElem(v___x_4160_, v_dec_4035_, v___x_4036_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4161_;
}
}
}
case 1:
{
lean_dec(v___y_4037_);
if (lean_obj_tag(v_otherwise_x3f_4028_) == 1)
{
lean_object* v___x_4168_; 
lean_dec_ref_known(v_otherwise_x3f_4028_, 1);
lean_dec_ref(v_dec_4035_);
lean_dec(v___x_4034_);
lean_dec(v___x_4033_);
lean_dec_ref(v___x_4032_);
lean_dec_ref(v___x_4031_);
lean_dec_ref(v___x_4030_);
v___x_4168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4168_;
}
else
{
lean_object* v_ref_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
lean_dec(v_otherwise_x3f_4028_);
v_ref_4169_ = lean_ctor_get(v___y_4045_, 5);
v___x_4170_ = l_Lean_SourceInfo_fromRef(v_ref_4169_, v___x_4029_);
v___x_4171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4032_, 3);
lean_inc_ref_n(v___x_4031_, 3);
lean_inc_ref_n(v___x_4030_, 3);
v___x_4172_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4171_);
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4170_, 6);
v___x_4174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4170_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4176_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4175_);
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4178_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4170_);
lean_ctor_set(v___x_4179_, 1, v___x_4177_);
lean_ctor_set(v___x_4179_, 2, v___x_4178_);
lean_inc_ref_n(v___x_4179_, 2);
v___x_4180_ = l_Lean_Syntax_node1(v___x_4170_, v___x_4176_, v___x_4179_);
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4182_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4181_);
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4184_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4183_);
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4170_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = l_Lean_Syntax_node5(v___x_4170_, v___x_4184_, v___x_4033_, v___x_4179_, v___x_4179_, v___x_4186_, v___x_4034_);
v___x_4188_ = l_Lean_Syntax_node1(v___x_4170_, v___x_4182_, v___x_4187_);
v___x_4189_ = l_Lean_Syntax_node3(v___x_4170_, v___x_4172_, v___x_4174_, v___x_4180_, v___x_4188_);
v___x_4190_ = l_Lean_Elab_Do_elabDoElem(v___x_4189_, v_dec_4035_, v___x_4036_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4190_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4028_);
if (lean_obj_tag(v___y_4037_) == 0)
{
v___y_4071_ = v___x_4039_;
goto v___jp_4070_;
}
else
{
lean_dec_ref_known(v___y_4037_, 1);
v___y_4071_ = v___x_4029_;
goto v___jp_4070_;
}
}
}
v___jp_4048_:
{
lean_object* v_ref_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_ref_4056_ = lean_ctor_get(v___y_4054_, 5);
v___x_4057_ = l_Lean_SourceInfo_fromRef(v_ref_4056_, v___x_4029_);
v___x_4058_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4032_);
lean_inc_ref(v___x_4031_);
lean_inc_ref(v___x_4030_);
v___x_4059_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4058_);
v___x_4060_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4061_ = l_Lean_Name_mkStr4(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4060_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4063_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4057_, 3);
v___x_4064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4057_);
lean_ctor_set(v___x_4064_, 1, v___x_4062_);
lean_ctor_set(v___x_4064_, 2, v___x_4063_);
v___x_4065_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4057_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
lean_inc_ref(v___x_4064_);
v___x_4067_ = l_Lean_Syntax_node5(v___x_4057_, v___x_4061_, v___x_4033_, v___x_4064_, v___x_4064_, v___x_4066_, v___x_4034_);
v___x_4068_ = l_Lean_Syntax_node1(v___x_4057_, v___x_4059_, v___x_4067_);
v___x_4069_ = l_Lean_Elab_Do_elabDoElem(v___x_4068_, v_dec_4035_, v___x_4036_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
return v___x_4069_;
}
v___jp_4070_:
{
if (v___y_4071_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v_dec_4035_);
lean_dec(v___x_4034_);
lean_dec(v___x_4033_);
lean_dec_ref(v___x_4032_);
lean_dec_ref(v___x_4031_);
lean_dec_ref(v___x_4030_);
v___x_4072_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4073_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4072_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
else
{
v___y_4049_ = v___y_4040_;
v___y_4050_ = v___y_4041_;
v___y_4051_ = v___y_4042_;
v___y_4052_ = v___y_4043_;
v___y_4053_ = v___y_4044_;
v___y_4054_ = v___y_4045_;
v___y_4055_ = v___y_4046_;
goto v___jp_4048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4191_ = _args[0];
lean_object* v_otherwise_x3f_4192_ = _args[1];
lean_object* v___x_4193_ = _args[2];
lean_object* v___x_4194_ = _args[3];
lean_object* v___x_4195_ = _args[4];
lean_object* v___x_4196_ = _args[5];
lean_object* v___x_4197_ = _args[6];
lean_object* v___x_4198_ = _args[7];
lean_object* v_dec_4199_ = _args[8];
lean_object* v___x_4200_ = _args[9];
lean_object* v___y_4201_ = _args[10];
lean_object* v___x_4202_ = _args[11];
lean_object* v___x_4203_ = _args[12];
lean_object* v___y_4204_ = _args[13];
lean_object* v___y_4205_ = _args[14];
lean_object* v___y_4206_ = _args[15];
lean_object* v___y_4207_ = _args[16];
lean_object* v___y_4208_ = _args[17];
lean_object* v___y_4209_ = _args[18];
lean_object* v___y_4210_ = _args[19];
lean_object* v___y_4211_ = _args[20];
_start:
{
uint8_t v___x_39383__boxed_4212_; uint8_t v___x_39389__boxed_4213_; uint8_t v___x_39392__boxed_4214_; lean_object* v_res_4215_; 
v___x_39383__boxed_4212_ = lean_unbox(v___x_4193_);
v___x_39389__boxed_4213_ = lean_unbox(v___x_4200_);
v___x_39392__boxed_4214_ = lean_unbox(v___x_4203_);
v_res_4215_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4191_, v_otherwise_x3f_4192_, v___x_39383__boxed_4212_, v___x_4194_, v___x_4195_, v___x_4196_, v___x_4197_, v___x_4198_, v_dec_4199_, v___x_39389__boxed_4213_, v___y_4201_, v___x_4202_, v___x_39392__boxed_4214_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___x_4202_);
lean_dec(v_letOrReassign_4191_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4236_, lean_object* v_stx_4237_, lean_object* v_tk_4238_, lean_object* v_dec_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4237_);
v___x_4252_ = l_Lean_Syntax_isOfKind(v_stx_4237_, v___x_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4253_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4237_);
v___x_4254_ = l_Lean_Syntax_isOfKind(v_stx_4237_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; 
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4255_;
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; 
v___x_4256_ = lean_unsigned_to_nat(0u);
v___x_4257_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4257_);
v___x_4259_ = l_Lean_Syntax_isOfKind(v___x_4257_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4345_; lean_object* v_patType_x3f_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4345_ = lean_unsigned_to_nat(1u);
v___x_4376_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4345_);
v___x_4377_ = l_Lean_Syntax_isNone(v___x_4376_);
if (v___x_4377_ == 0)
{
uint8_t v___x_4378_; 
lean_inc(v___x_4376_);
v___x_4378_ = l_Lean_Syntax_matchesNull(v___x_4376_, v___x_4345_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
lean_dec(v___x_4376_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4379_;
}
else
{
lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4380_ = l_Lean_Syntax_getArg(v___x_4376_, v___x_4256_);
lean_dec(v___x_4376_);
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4380_);
v___x_4382_ = l_Lean_Syntax_isOfKind(v___x_4380_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; 
lean_dec(v___x_4380_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4383_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4383_;
}
else
{
lean_object* v_patType_x3f_4384_; lean_object* v___x_4385_; 
v_patType_x3f_4384_ = l_Lean_Syntax_getArg(v___x_4380_, v___x_4345_);
lean_dec(v___x_4380_);
v___x_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4385_, 0, v_patType_x3f_4384_);
v_patType_x3f_4347_ = v___x_4385_;
v___y_4348_ = v_a_4240_;
v___y_4349_ = v_a_4241_;
v___y_4350_ = v_a_4242_;
v___y_4351_ = v_a_4243_;
v___y_4352_ = v_a_4244_;
v___y_4353_ = v_a_4245_;
v___y_4354_ = v_a_4246_;
goto v___jp_4346_;
}
}
}
else
{
lean_object* v___x_4386_; 
lean_dec(v___x_4376_);
v___x_4386_ = lean_box(0);
v_patType_x3f_4347_ = v___x_4386_;
v___y_4348_ = v_a_4240_;
v___y_4349_ = v_a_4241_;
v___y_4350_ = v_a_4242_;
v___y_4351_ = v_a_4243_;
v___y_4352_ = v_a_4244_;
v___y_4353_ = v_a_4245_;
v___y_4354_ = v_a_4246_;
goto v___jp_4346_;
}
v___jp_4346_:
{
lean_object* v___x_4355_; lean_object* v_rhs_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4355_ = lean_unsigned_to_nat(3u);
v_rhs_4356_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4355_);
v___x_4357_ = lean_unsigned_to_nat(4u);
v___x_4358_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4357_);
lean_dec(v_stx_4237_);
v___x_4359_ = l_Lean_Syntax_isNone(v___x_4358_);
if (v___x_4359_ == 0)
{
uint8_t v___x_4360_; 
lean_inc(v___x_4358_);
v___x_4360_ = l_Lean_Syntax_matchesNull(v___x_4358_, v___x_4355_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; 
lean_dec(v___x_4358_);
lean_dec(v_rhs_4356_);
lean_dec(v_patType_x3f_4347_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_letOrReassign_4236_);
v___x_4361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4361_;
}
else
{
lean_object* v___x_4362_; lean_object* v_otherwise_x3f_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4363_ = l_Lean_Syntax_getArg(v___x_4358_, v___x_4345_);
v___x_4364_ = l_Lean_Syntax_getArg(v___x_4358_, v___x_4362_);
lean_dec(v___x_4358_);
v___x_4365_ = l_Lean_Syntax_getOptional_x3f(v___x_4364_);
lean_dec(v___x_4364_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v___x_4366_; 
v___x_4366_ = lean_box(0);
v___y_4290_ = v___y_4354_;
v___y_4291_ = v___y_4349_;
v___y_4292_ = v___y_4350_;
v___y_4293_ = v_rhs_4356_;
v___y_4294_ = v_otherwise_x3f_4363_;
v___y_4295_ = v___y_4351_;
v___y_4296_ = v___y_4352_;
v___y_4297_ = v___y_4348_;
v___y_4298_ = v___y_4353_;
v___y_4299_ = v_patType_x3f_4347_;
v___y_4300_ = v___x_4366_;
goto v___jp_4289_;
}
else
{
lean_object* v_val_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_val_4367_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4365_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_val_4367_);
lean_dec(v___x_4365_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_val_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
v___y_4290_ = v___y_4354_;
v___y_4291_ = v___y_4349_;
v___y_4292_ = v___y_4350_;
v___y_4293_ = v_rhs_4356_;
v___y_4294_ = v_otherwise_x3f_4363_;
v___y_4295_ = v___y_4351_;
v___y_4296_ = v___y_4352_;
v___y_4297_ = v___y_4348_;
v___y_4298_ = v___y_4353_;
v___y_4299_ = v_patType_x3f_4347_;
v___y_4300_ = v___x_4372_;
goto v___jp_4289_;
}
}
}
}
}
else
{
lean_object* v___x_4375_; 
lean_dec(v___x_4358_);
v___x_4375_ = lean_box(0);
v___y_4261_ = v___y_4349_;
v___y_4262_ = v_patType_x3f_4347_;
v___y_4263_ = v___x_4375_;
v___y_4264_ = v___y_4353_;
v___y_4265_ = v_rhs_4356_;
v___y_4266_ = v___y_4354_;
v___y_4267_ = v___y_4348_;
v___y_4268_ = v___y_4350_;
v___y_4269_ = v___y_4352_;
v___y_4270_ = v___y_4351_;
v___y_4271_ = v___x_4375_;
goto v___jp_4260_;
}
}
}
else
{
lean_object* v_pattern_4387_; lean_object* v___x_4388_; lean_object* v_patType_x3f_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v_pattern_4387_ = l_Lean_Syntax_getArg(v___x_4257_, v___x_4256_);
v___x_4388_ = lean_unsigned_to_nat(1u);
v___x_4445_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4388_);
v___x_4446_ = l_Lean_Syntax_isNone(v___x_4445_);
if (v___x_4446_ == 0)
{
uint8_t v___x_4447_; 
lean_inc(v___x_4445_);
v___x_4447_ = l_Lean_Syntax_matchesNull(v___x_4445_, v___x_4388_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; 
lean_dec(v___x_4445_);
lean_dec(v_pattern_4387_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4448_;
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; 
v___x_4449_ = l_Lean_Syntax_getArg(v___x_4445_, v___x_4256_);
lean_dec(v___x_4445_);
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4449_);
v___x_4451_ = l_Lean_Syntax_isOfKind(v___x_4449_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; 
lean_dec(v___x_4449_);
lean_dec(v_pattern_4387_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4452_;
}
else
{
lean_object* v_patType_x3f_4453_; lean_object* v___x_4454_; 
v_patType_x3f_4453_ = l_Lean_Syntax_getArg(v___x_4449_, v___x_4388_);
lean_dec(v___x_4449_);
v___x_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4454_, 0, v_patType_x3f_4453_);
v_patType_x3f_4390_ = v___x_4454_;
v___y_4391_ = v_a_4240_;
v___y_4392_ = v_a_4241_;
v___y_4393_ = v_a_4242_;
v___y_4394_ = v_a_4243_;
v___y_4395_ = v_a_4244_;
v___y_4396_ = v_a_4245_;
v___y_4397_ = v_a_4246_;
goto v___jp_4389_;
}
}
}
else
{
lean_object* v___x_4455_; 
lean_dec(v___x_4445_);
v___x_4455_ = lean_box(0);
v_patType_x3f_4390_ = v___x_4455_;
v___y_4391_ = v_a_4240_;
v___y_4392_ = v_a_4241_;
v___y_4393_ = v_a_4242_;
v___y_4394_ = v_a_4243_;
v___y_4395_ = v_a_4244_;
v___y_4396_ = v_a_4245_;
v___y_4397_ = v_a_4246_;
goto v___jp_4389_;
}
v___jp_4389_:
{
lean_object* v___x_4398_; lean_object* v_rhs_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
v___x_4398_ = lean_unsigned_to_nat(3u);
v_rhs_4399_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4398_);
v___x_4400_ = lean_unsigned_to_nat(4u);
v___x_4401_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4400_);
lean_dec(v_stx_4237_);
lean_inc(v___x_4401_);
v___x_4402_ = l_Lean_Syntax_matchesNull(v___x_4401_, v___x_4256_);
if (v___x_4402_ == 0)
{
uint8_t v___x_4403_; 
lean_dec(v_pattern_4387_);
v___x_4403_ = l_Lean_Syntax_isNone(v___x_4401_);
if (v___x_4403_ == 0)
{
uint8_t v___x_4404_; 
lean_inc(v___x_4401_);
v___x_4404_ = l_Lean_Syntax_matchesNull(v___x_4401_, v___x_4398_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; 
lean_dec(v___x_4401_);
lean_dec(v_rhs_4399_);
lean_dec(v_patType_x3f_4390_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_letOrReassign_4236_);
v___x_4405_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4405_;
}
else
{
lean_object* v___x_4406_; lean_object* v_otherwise_x3f_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4406_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4407_ = l_Lean_Syntax_getArg(v___x_4401_, v___x_4388_);
v___x_4408_ = l_Lean_Syntax_getArg(v___x_4401_, v___x_4406_);
lean_dec(v___x_4401_);
v___x_4409_ = l_Lean_Syntax_getOptional_x3f(v___x_4408_);
lean_dec(v___x_4408_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_box(0);
v___y_4333_ = v_patType_x3f_4390_;
v___y_4334_ = v___y_4391_;
v___y_4335_ = v___y_4393_;
v___y_4336_ = v_rhs_4399_;
v___y_4337_ = v___y_4394_;
v___y_4338_ = v___y_4397_;
v___y_4339_ = v_otherwise_x3f_4407_;
v___y_4340_ = v___y_4396_;
v___y_4341_ = v___y_4392_;
v___y_4342_ = v___y_4395_;
v___y_4343_ = v___x_4410_;
goto v___jp_4332_;
}
else
{
lean_object* v_val_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_val_4411_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4409_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_val_4411_);
lean_dec(v___x_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_val_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
v___y_4333_ = v_patType_x3f_4390_;
v___y_4334_ = v___y_4391_;
v___y_4335_ = v___y_4393_;
v___y_4336_ = v_rhs_4399_;
v___y_4337_ = v___y_4394_;
v___y_4338_ = v___y_4397_;
v___y_4339_ = v_otherwise_x3f_4407_;
v___y_4340_ = v___y_4396_;
v___y_4341_ = v___y_4392_;
v___y_4342_ = v___y_4395_;
v___y_4343_ = v___x_4416_;
goto v___jp_4332_;
}
}
}
}
}
else
{
lean_object* v___x_4419_; 
lean_dec(v___x_4401_);
v___x_4419_ = lean_box(0);
v___y_4303_ = v___y_4392_;
v___y_4304_ = v___y_4391_;
v___y_4305_ = v_patType_x3f_4390_;
v___y_4306_ = v___y_4396_;
v___y_4307_ = v___y_4397_;
v___y_4308_ = v___y_4393_;
v___y_4309_ = v_rhs_4399_;
v___y_4310_ = v___y_4395_;
v___y_4311_ = v___y_4394_;
v___y_4312_ = v___x_4419_;
v___y_4313_ = v___x_4419_;
goto v___jp_4302_;
}
}
else
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_dec(v___x_4401_);
lean_dec(v___x_4257_);
lean_dec(v_letOrReassign_4236_);
v___x_4420_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4421_ = l_Lean_Core_mkFreshUserName(v___x_4420_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4239_, v_tk_4238_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; uint8_t v_kind_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v_kind_4425_ = lean_ctor_get_uint8(v_a_4424_, sizeof(void*)*3);
v___x_4426_ = l_Lean_mkIdentFrom(v_pattern_4387_, v_a_4422_, v___x_4252_);
lean_dec(v_pattern_4387_);
v___x_4427_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4427_, 0, v_a_4424_);
v___x_4428_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4426_, v_patType_x3f_4390_, v_rhs_4399_, v___x_4427_, v_kind_4425_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4428_;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4422_);
lean_dec(v_rhs_4399_);
lean_dec(v_patType_x3f_4390_);
lean_dec(v_pattern_4387_);
v_a_4429_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4423_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4423_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_rhs_4399_);
lean_dec(v_patType_x3f_4390_);
lean_dec(v_pattern_4387_);
lean_dec_ref(v_dec_4239_);
v_a_4437_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4421_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4421_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
}
v___jp_4260_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4273_ = l_Lean_Core_mkFreshUserName(v___x_4272_, v___y_4264_, v___y_4266_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___y_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4275_ = l_Lean_mkIdentFrom(v___x_4257_, v_a_4274_, v___x_4259_);
v___x_4276_ = lean_box(v___x_4259_);
v___x_4277_ = lean_box(v___x_4254_);
lean_inc(v___x_4275_);
v___y_4278_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4278_, 0, v_letOrReassign_4236_);
lean_closure_set(v___y_4278_, 1, v___y_4263_);
lean_closure_set(v___y_4278_, 2, v___x_4276_);
lean_closure_set(v___y_4278_, 3, v___x_4248_);
lean_closure_set(v___y_4278_, 4, v___x_4249_);
lean_closure_set(v___y_4278_, 5, v___x_4250_);
lean_closure_set(v___y_4278_, 6, v___x_4257_);
lean_closure_set(v___y_4278_, 7, v___x_4275_);
lean_closure_set(v___y_4278_, 8, v_dec_4239_);
lean_closure_set(v___y_4278_, 9, v___x_4277_);
lean_closure_set(v___y_4278_, 10, v___y_4271_);
lean_closure_set(v___y_4278_, 11, v___x_4256_);
v___x_4279_ = 0;
v___x_4280_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4275_, v___y_4262_, v___y_4265_, v___y_4278_, v___x_4279_, v___y_4267_, v___y_4261_, v___y_4268_, v___y_4270_, v___y_4269_, v___y_4264_, v___y_4266_);
return v___x_4280_;
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v___y_4271_);
lean_dec(v___y_4265_);
lean_dec(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_letOrReassign_4236_);
v_a_4281_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4273_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4273_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
v___jp_4289_:
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___y_4294_);
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4299_;
v___y_4263_ = v___x_4301_;
v___y_4264_ = v___y_4298_;
v___y_4265_ = v___y_4293_;
v___y_4266_ = v___y_4290_;
v___y_4267_ = v___y_4297_;
v___y_4268_ = v___y_4292_;
v___y_4269_ = v___y_4296_;
v___y_4270_ = v___y_4295_;
v___y_4271_ = v___y_4300_;
goto v___jp_4260_;
}
v___jp_4302_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4315_ = l_Lean_Core_mkFreshUserName(v___x_4314_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___y_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = l_Lean_mkIdentFrom(v___x_4257_, v_a_4316_, v___x_4252_);
v___x_4318_ = lean_box(v___x_4252_);
v___x_4319_ = lean_box(v___x_4254_);
v___x_4320_ = lean_box(v___x_4259_);
lean_inc(v___x_4317_);
v___y_4321_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4321_, 0, v_letOrReassign_4236_);
lean_closure_set(v___y_4321_, 1, v___y_4312_);
lean_closure_set(v___y_4321_, 2, v___x_4318_);
lean_closure_set(v___y_4321_, 3, v___x_4248_);
lean_closure_set(v___y_4321_, 4, v___x_4249_);
lean_closure_set(v___y_4321_, 5, v___x_4250_);
lean_closure_set(v___y_4321_, 6, v___x_4257_);
lean_closure_set(v___y_4321_, 7, v___x_4317_);
lean_closure_set(v___y_4321_, 8, v_dec_4239_);
lean_closure_set(v___y_4321_, 9, v___x_4319_);
lean_closure_set(v___y_4321_, 10, v___y_4313_);
lean_closure_set(v___y_4321_, 11, v___x_4256_);
lean_closure_set(v___y_4321_, 12, v___x_4320_);
v___x_4322_ = 0;
v___x_4323_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4317_, v___y_4305_, v___y_4309_, v___y_4321_, v___x_4322_, v___y_4304_, v___y_4303_, v___y_4308_, v___y_4311_, v___y_4310_, v___y_4306_, v___y_4307_);
return v___x_4323_;
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec(v___y_4309_);
lean_dec(v___y_4305_);
lean_dec(v___x_4257_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_letOrReassign_4236_);
v_a_4324_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4315_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4315_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
v___jp_4332_:
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___y_4339_);
v___y_4303_ = v___y_4341_;
v___y_4304_ = v___y_4334_;
v___y_4305_ = v___y_4333_;
v___y_4306_ = v___y_4340_;
v___y_4307_ = v___y_4338_;
v___y_4308_ = v___y_4335_;
v___y_4309_ = v___y_4336_;
v___y_4310_ = v___y_4342_;
v___y_4311_ = v___y_4337_;
v___y_4312_ = v___x_4344_;
v___y_4313_ = v___y_4343_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v___x_4456_; lean_object* v_x_4457_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v_xType_x3f_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v_xType_x3f_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v_x_4457_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4456_);
v___x_4530_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4457_);
v___x_4531_ = l_Lean_Syntax_isOfKind(v_x_4457_, v___x_4530_);
if (v___x_4531_ == 0)
{
lean_object* v___x_4532_; 
lean_dec(v_x_4457_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4532_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4534_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4533_);
v___x_4535_ = l_Lean_Syntax_isNone(v___x_4534_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
lean_inc(v___x_4534_);
v___x_4536_ = l_Lean_Syntax_matchesNull(v___x_4534_, v___x_4533_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_dec(v___x_4534_);
lean_dec(v_x_4457_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4538_ = l_Lean_Syntax_getArg(v___x_4534_, v___x_4456_);
lean_dec(v___x_4534_);
v___x_4539_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4538_);
v___x_4540_ = l_Lean_Syntax_isOfKind(v___x_4538_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_dec(v___x_4538_);
lean_dec(v_x_4457_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v___x_4541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4541_;
}
else
{
lean_object* v_xType_x3f_4542_; lean_object* v___x_4543_; 
v_xType_x3f_4542_ = l_Lean_Syntax_getArg(v___x_4538_, v___x_4533_);
lean_dec(v___x_4538_);
v___x_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_xType_x3f_4542_);
v_xType_x3f_4475_ = v___x_4543_;
v___y_4476_ = v_a_4240_;
v___y_4477_ = v_a_4241_;
v___y_4478_ = v_a_4242_;
v___y_4479_ = v_a_4243_;
v___y_4480_ = v_a_4244_;
v___y_4481_ = v_a_4245_;
v___y_4482_ = v_a_4246_;
goto v___jp_4474_;
}
}
}
else
{
lean_object* v___x_4544_; 
lean_dec(v___x_4534_);
v___x_4544_ = lean_box(0);
v_xType_x3f_4475_ = v___x_4544_;
v___y_4476_ = v_a_4240_;
v___y_4477_ = v_a_4241_;
v___y_4478_ = v_a_4242_;
v___y_4479_ = v_a_4243_;
v___y_4480_ = v_a_4244_;
v___y_4481_ = v_a_4245_;
v___y_4482_ = v_a_4246_;
goto v___jp_4474_;
}
}
v___jp_4458_:
{
uint8_t v_kind_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v_kind_4469_ = lean_ctor_get_uint8(v___y_4459_, sizeof(void*)*3);
v___x_4470_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4236_);
lean_dec(v_letOrReassign_4236_);
v___x_4471_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4471_, 0, v___y_4459_);
lean_inc(v_x_4457_);
v___x_4472_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4472_, 0, lean_box(0));
lean_closure_set(v___x_4472_, 1, v___x_4470_);
lean_closure_set(v___x_4472_, 2, v_x_4457_);
lean_closure_set(v___x_4472_, 3, v___x_4471_);
v___x_4473_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4457_, v_xType_x3f_4461_, v___y_4460_, v___x_4472_, v_kind_4469_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4473_;
}
v___jp_4474_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4483_ = lean_unsigned_to_nat(1u);
v___x_4484_ = lean_mk_empty_array_with_capacity(v___x_4483_);
lean_inc(v_x_4457_);
v___x_4485_ = lean_array_push(v___x_4484_, v_x_4457_);
v___x_4486_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4236_, v___x_4485_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec_ref(v___x_4485_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v___x_4487_; 
lean_dec_ref_known(v___x_4486_, 1);
v___x_4487_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4239_, v_tk_4238_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4489_; lean_object* v_rhs_4490_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
v___x_4489_ = lean_unsigned_to_nat(3u);
v_rhs_4490_ = l_Lean_Syntax_getArg(v_stx_4237_, v___x_4489_);
lean_dec(v_stx_4237_);
if (lean_obj_tag(v_letOrReassign_4236_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4475_) == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4491_ = l_Lean_TSyntax_getId(v_x_4457_);
v___x_4492_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4491_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v___x_4492_, 1);
v___x_4494_ = l_Lean_LocalDecl_type(v_a_4493_);
lean_dec(v_a_4493_);
v___x_4495_ = l_Lean_Elab_Term_exprToSyntax(v___x_4494_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4497_, 0, v_a_4496_);
v___y_4459_ = v_a_4488_;
v___y_4460_ = v_rhs_4490_;
v_xType_x3f_4461_ = v___x_4497_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
goto v___jp_4458_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_rhs_4490_);
lean_dec(v_a_4488_);
lean_dec(v_x_4457_);
v_a_4498_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4495_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4495_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_rhs_4490_);
lean_dec(v_a_4488_);
lean_dec(v_x_4457_);
v_a_4506_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4492_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4492_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
v___y_4459_ = v_a_4488_;
v___y_4460_ = v_rhs_4490_;
v_xType_x3f_4461_ = v_xType_x3f_4475_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
goto v___jp_4458_;
}
}
else
{
v___y_4459_ = v_a_4488_;
v___y_4460_ = v_rhs_4490_;
v_xType_x3f_4461_ = v_xType_x3f_4475_;
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
goto v___jp_4458_;
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v_xType_x3f_4475_);
lean_dec(v_x_4457_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v_a_4514_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4487_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4487_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
lean_dec(v_xType_x3f_4475_);
lean_dec(v_x_4457_);
lean_dec_ref(v_dec_4239_);
lean_dec(v_stx_4237_);
lean_dec(v_letOrReassign_4236_);
v_a_4522_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4486_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4486_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4545_, lean_object* v_stx_4546_, lean_object* v_tk_4547_, lean_object* v_dec_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4545_, v_stx_4546_, v_tk_4547_, v_dec_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_tk_4547_);
return v_res_4557_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4560_ = l_Lean_stringToMessageData(v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4561_, lean_object* v_mutTk_x3f_4562_, lean_object* v_initConfig_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4562_) == 0)
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4561_, v_initConfig_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = l_Lean_Syntax_getArg(v_letConfigStx_4561_, v___x_4572_);
v___x_4574_ = l_Lean_Syntax_getArgs(v___x_4573_);
lean_dec(v___x_4573_);
v___x_4575_ = lean_array_get_size(v___x_4574_);
lean_dec_ref(v___x_4574_);
v___x_4576_ = lean_nat_dec_eq(v___x_4575_, v___x_4572_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_initConfig_4563_);
v___x_4577_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4578_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4561_, v___x_4577_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_letConfigStx_4561_);
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4578_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4578_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
else
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4561_, v_initConfig_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4588_, lean_object* v_mutTk_x3f_4589_, lean_object* v_initConfig_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4588_, v_mutTk_x3f_4589_, v_initConfig_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_mutTk_x3f_4589_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4599_, lean_object* v_mutTk_x3f_4600_, lean_object* v_initConfig_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v___x_4610_; 
v___x_4610_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4599_, v_mutTk_x3f_4600_, v_initConfig_4601_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4611_, lean_object* v_mutTk_x3f_4612_, lean_object* v_initConfig_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4611_, v_mutTk_x3f_4612_, v_initConfig_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_mutTk_x3f_4612_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4636_, lean_object* v_dec_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4646_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4636_);
v___x_4647_ = l_Lean_Syntax_isOfKind(v_stx_4636_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4648_; 
lean_dec_ref(v_dec_4637_);
lean_dec(v_stx_4636_);
v___x_4648_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4648_;
}
else
{
lean_object* v___x_4649_; lean_object* v_tk_4650_; lean_object* v_mutTk_x3f_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v_tk_4650_ = l_Lean_Syntax_getArg(v_stx_4636_, v___x_4649_);
v___x_4683_ = lean_unsigned_to_nat(1u);
v___x_4684_ = l_Lean_Syntax_getArg(v_stx_4636_, v___x_4683_);
v___x_4685_ = l_Lean_Syntax_isNone(v___x_4684_);
if (v___x_4685_ == 0)
{
uint8_t v___x_4686_; 
lean_inc(v___x_4684_);
v___x_4686_ = l_Lean_Syntax_matchesNull(v___x_4684_, v___x_4683_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; 
lean_dec(v___x_4684_);
lean_dec(v_tk_4650_);
lean_dec_ref(v_dec_4637_);
lean_dec(v_stx_4636_);
v___x_4687_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4687_;
}
else
{
lean_object* v_mutTk_x3f_4688_; lean_object* v___x_4689_; 
v_mutTk_x3f_4688_ = l_Lean_Syntax_getArg(v___x_4684_, v___x_4649_);
lean_dec(v___x_4684_);
v___x_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4689_, 0, v_mutTk_x3f_4688_);
v_mutTk_x3f_4652_ = v___x_4689_;
v___y_4653_ = v_a_4638_;
v___y_4654_ = v_a_4639_;
v___y_4655_ = v_a_4640_;
v___y_4656_ = v_a_4641_;
v___y_4657_ = v_a_4642_;
v___y_4658_ = v_a_4643_;
v___y_4659_ = v_a_4644_;
goto v___jp_4651_;
}
}
else
{
lean_object* v___x_4690_; 
lean_dec(v___x_4684_);
v___x_4690_ = lean_box(0);
v_mutTk_x3f_4652_ = v___x_4690_;
v___y_4653_ = v_a_4638_;
v___y_4654_ = v_a_4639_;
v___y_4655_ = v_a_4640_;
v___y_4656_ = v_a_4641_;
v___y_4657_ = v_a_4642_;
v___y_4658_ = v_a_4643_;
v___y_4659_ = v_a_4644_;
goto v___jp_4651_;
}
v___jp_4651_:
{
lean_object* v___x_4660_; lean_object* v_config_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4660_ = lean_unsigned_to_nat(2u);
v_config_4661_ = l_Lean_Syntax_getArg(v_stx_4636_, v___x_4660_);
v___x_4662_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4661_);
v___x_4663_ = l_Lean_Syntax_isOfKind(v_config_4661_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; 
lean_dec(v_config_4661_);
lean_dec(v_mutTk_x3f_4652_);
lean_dec(v_tk_4650_);
lean_dec_ref(v_dec_4637_);
lean_dec(v_stx_4636_);
v___x_4664_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4664_;
}
else
{
lean_object* v___x_4665_; lean_object* v_decl_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4665_ = lean_unsigned_to_nat(3u);
v_decl_4666_ = l_Lean_Syntax_getArg(v_stx_4636_, v___x_4665_);
lean_dec(v_stx_4636_);
v___x_4667_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4666_);
v___x_4668_ = l_Lean_Syntax_isOfKind(v_decl_4666_, v___x_4667_);
if (v___x_4668_ == 0)
{
lean_object* v___x_4669_; 
lean_dec(v_decl_4666_);
lean_dec(v_config_4661_);
lean_dec(v_mutTk_x3f_4652_);
lean_dec(v_tk_4650_);
lean_dec_ref(v_dec_4637_);
v___x_4669_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4669_;
}
else
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4671_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4661_, v_mutTk_x3f_4652_, v___x_4670_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v_mutTk_x3f_4652_);
v___x_4674_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4672_, v___x_4673_, v_decl_4666_, v_tk_4650_, v_dec_4637_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
return v___x_4674_;
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
lean_dec(v_decl_4666_);
lean_dec(v_mutTk_x3f_4652_);
lean_dec(v_tk_4650_);
lean_dec_ref(v_dec_4637_);
v_a_4675_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4671_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4671_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4691_, lean_object* v_dec_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Elab_Do_elabDoLet(v_stx_4691_, v_dec_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec_ref(v_a_4693_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4709_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4710_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4711_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4712_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4713_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4709_, v___x_4710_, v___x_4711_, v___x_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4721_, lean_object* v_dec_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4721_);
v___x_4732_ = l_Lean_Syntax_isOfKind(v_stx_4721_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; 
lean_dec_ref(v_dec_4722_);
lean_dec(v_stx_4721_);
v___x_4733_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = l_Lean_Syntax_getArg(v_stx_4721_, v___x_4734_);
v___x_4736_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4735_);
v___x_4737_ = l_Lean_Syntax_isOfKind(v___x_4735_, v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; 
lean_dec(v___x_4735_);
lean_dec_ref(v_dec_4722_);
lean_dec(v_stx_4721_);
v___x_4738_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4738_;
}
else
{
lean_object* v___x_4739_; lean_object* v_decl_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4739_ = lean_unsigned_to_nat(2u);
v_decl_4740_ = l_Lean_Syntax_getArg(v_stx_4721_, v___x_4739_);
v___x_4741_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4740_);
v___x_4742_ = l_Lean_Syntax_isOfKind(v_decl_4740_, v___x_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; 
lean_dec(v_decl_4740_);
lean_dec(v___x_4735_);
lean_dec_ref(v_dec_4722_);
lean_dec(v_stx_4721_);
v___x_4743_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4743_;
}
else
{
uint8_t v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4744_ = 0;
v___x_4745_ = lean_box(0);
v___x_4746_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1, v___x_4742_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1 + 1, v___x_4744_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1 + 2, v___x_4744_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1 + 3, v___x_4744_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1 + 4, v___x_4744_);
v___x_4747_ = l_Lean_Elab_Term_mkLetConfig(v___x_4735_, v___x_4746_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4749_; lean_object* v_tk_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4747_, 1);
v___x_4749_ = lean_unsigned_to_nat(0u);
v_tk_4750_ = l_Lean_Syntax_getArg(v_stx_4721_, v___x_4749_);
lean_dec(v_stx_4721_);
v___x_4751_ = lean_box(1);
v___x_4752_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4748_, v___x_4751_, v_decl_4740_, v_tk_4750_, v_dec_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
return v___x_4752_;
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v_decl_4740_);
lean_dec_ref(v_dec_4722_);
lean_dec(v_stx_4721_);
v_a_4753_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4747_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4747_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4761_, lean_object* v_dec_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_Elab_Do_elabDoHave(v_stx_4761_, v_dec_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec_ref(v_a_4763_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4779_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4780_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4781_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4782_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4783_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4779_, v___x_4780_, v___x_4781_, v___x_4782_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4788_, lean_object* v___x_4789_, lean_object* v___x_4790_, lean_object* v___x_4791_, lean_object* v_decls_4792_, lean_object* v_a_4793_, uint8_t v___x_4794_, lean_object* v_body_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_ref_4804_; uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v_ref_4804_ = lean_ctor_get(v___y_4801_, 5);
v___x_4805_ = 0;
v___x_4806_ = l_Lean_SourceInfo_fromRef(v_ref_4804_, v___x_4805_);
v___x_4807_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4808_ = l_Lean_Name_mkStr4(v___x_4788_, v___x_4789_, v___x_4790_, v___x_4807_);
v___x_4809_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4806_, 4);
v___x_4810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4806_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
v___x_4811_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4806_);
lean_ctor_set(v___x_4812_, 1, v___x_4811_);
v___x_4813_ = l_Lean_Syntax_node2(v___x_4806_, v___x_4791_, v___x_4810_, v___x_4812_);
v___x_4814_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4806_);
lean_ctor_set(v___x_4815_, 1, v___x_4814_);
v___x_4816_ = l_Lean_Syntax_node4(v___x_4806_, v___x_4808_, v___x_4813_, v_decls_4792_, v___x_4815_, v_body_4795_);
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_a_4793_);
v___x_4818_ = l_Lean_Elab_Term_elabTerm(v___x_4816_, v___x_4817_, v___x_4794_, v___x_4794_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4819_, lean_object* v___x_4820_, lean_object* v___x_4821_, lean_object* v___x_4822_, lean_object* v_decls_4823_, lean_object* v_a_4824_, lean_object* v___x_4825_, lean_object* v_body_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
uint8_t v___x_5027__boxed_4835_; lean_object* v_res_4836_; 
v___x_5027__boxed_4835_ = lean_unbox(v___x_4825_);
v_res_4836_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4819_, v___x_4820_, v___x_4821_, v___x_4822_, v_decls_4823_, v_a_4824_, v___x_5027__boxed_4835_, v_body_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec_ref(v___y_4827_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
if (lean_obj_tag(v_a_4837_) == 0)
{
lean_object* v___x_4839_; 
v___x_4839_ = l_List_reverse___redArg(v_a_4838_);
return v___x_4839_;
}
else
{
lean_object* v_head_4840_; lean_object* v_tail_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4850_; 
v_head_4840_ = lean_ctor_get(v_a_4837_, 0);
v_tail_4841_ = lean_ctor_get(v_a_4837_, 1);
v_isSharedCheck_4850_ = !lean_is_exclusive(v_a_4837_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4843_ = v_a_4837_;
v_isShared_4844_ = v_isSharedCheck_4850_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_tail_4841_);
lean_inc(v_head_4840_);
lean_dec(v_a_4837_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4850_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4845_ = l_Lean_MessageData_ofSyntax(v_head_4840_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 1, v_a_4838_);
lean_ctor_set(v___x_4843_, 0, v___x_4845_);
v___x_4847_ = v___x_4843_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v_a_4838_);
v___x_4847_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
v_a_4837_ = v_tail_4841_;
v_a_4838_ = v___x_4847_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4868_ = l_Lean_stringToMessageData(v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4869_, lean_object* v_dec_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4880_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4881_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4882_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4869_);
v___x_4883_ = l_Lean_Syntax_isOfKind(v_stx_4869_, v___x_4882_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; 
lean_dec_ref(v_dec_4870_);
lean_dec(v_stx_4869_);
v___x_4884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4884_;
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; uint8_t v___x_4888_; 
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = l_Lean_Syntax_getArg(v_stx_4869_, v___x_4885_);
v___x_4887_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4886_);
v___x_4888_ = l_Lean_Syntax_isOfKind(v___x_4886_, v___x_4887_);
if (v___x_4888_ == 0)
{
lean_object* v___x_4889_; 
lean_dec(v___x_4886_);
lean_dec_ref(v_dec_4870_);
lean_dec(v_stx_4869_);
v___x_4889_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4889_;
}
else
{
lean_object* v___x_4890_; lean_object* v_decls_4891_; lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4890_ = lean_unsigned_to_nat(1u);
v_decls_4891_ = l_Lean_Syntax_getArg(v_stx_4869_, v___x_4890_);
lean_dec(v_stx_4869_);
v___x_4892_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4891_);
v___x_4893_ = l_Lean_Syntax_isOfKind(v_decls_4891_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; 
lean_dec(v_decls_4891_);
lean_dec(v___x_4886_);
lean_dec_ref(v_dec_4870_);
v___x_4894_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4894_;
}
else
{
lean_object* v_tk_4895_; lean_object* v___x_4896_; 
v_tk_4895_ = l_Lean_Syntax_getArg(v___x_4886_, v___x_4885_);
lean_dec(v___x_4886_);
v___x_4896_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4870_, v_tk_4895_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
lean_dec(v_tk_4895_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4898_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4896_, 1);
lean_inc(v_decls_4891_);
v___x_4898_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4891_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v_doBlockResultType_4900_; lean_object* v___x_4901_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref_known(v___x_4898_, 1);
v_doBlockResultType_4900_ = lean_ctor_get(v_a_4871_, 3);
lean_inc_ref(v_doBlockResultType_4900_);
v___x_4901_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4900_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4903_; lean_object* v___f_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4902_);
lean_dec_ref_known(v___x_4901_, 1);
v___x_4903_ = lean_box(v___x_4893_);
v___f_4904_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4904_, 0, v___x_4879_);
lean_closure_set(v___f_4904_, 1, v___x_4880_);
lean_closure_set(v___f_4904_, 2, v___x_4881_);
lean_closure_set(v___f_4904_, 3, v___x_4887_);
lean_closure_set(v___f_4904_, 4, v_decls_4891_);
lean_closure_set(v___f_4904_, 5, v_a_4902_);
lean_closure_set(v___f_4904_, 6, v___x_4903_);
v___x_4905_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4906_ = lean_array_to_list(v_a_4899_);
v___x_4907_ = lean_box(0);
v___x_4908_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4906_, v___x_4907_);
v___x_4909_ = l_Lean_MessageData_ofList(v___x_4908_);
v___x_4910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4905_);
lean_ctor_set(v___x_4910_, 1, v___x_4909_);
v___x_4911_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4911_, 0, v_a_4897_);
v___x_4912_ = lean_box(0);
v___x_4913_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4910_, v___x_4911_, v___f_4904_, v___x_4912_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
return v___x_4913_;
}
else
{
lean_dec(v_a_4899_);
lean_dec(v_a_4897_);
lean_dec(v_decls_4891_);
return v___x_4901_;
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
lean_dec(v_a_4897_);
lean_dec(v_decls_4891_);
v_a_4914_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4898_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4898_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec(v_decls_4891_);
v_a_4922_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4896_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4896_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4930_, lean_object* v_dec_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4930_, v_dec_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec_ref(v_a_4932_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4948_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4949_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4950_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4951_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4952_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4948_, v___x_4949_, v___x_4950_, v___x_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4968_, lean_object* v_dec_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; uint8_t v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v___x_5011_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4968_);
v___x_5012_ = l_Lean_Syntax_isOfKind(v_stx_4968_, v___x_5011_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
lean_dec_ref(v_dec_4969_);
lean_dec(v_stx_4968_);
v___x_5013_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5013_;
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; 
v___x_5014_ = lean_unsigned_to_nat(0u);
v___x_5015_ = l_Lean_Syntax_getArg(v_stx_4968_, v___x_5014_);
lean_dec(v_stx_4968_);
v___x_5016_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5015_);
v___x_5017_ = l_Lean_Syntax_isOfKind(v___x_5015_, v___x_5016_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; uint8_t v___x_5019_; 
v___x_5018_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5015_);
v___x_5019_ = l_Lean_Syntax_isOfKind(v___x_5015_, v___x_5018_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5020_;
}
else
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v_decl_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5021_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5022_ = lean_unsigned_to_nat(1u);
v___x_5023_ = lean_mk_empty_array_with_capacity(v___x_5022_);
v___x_5024_ = lean_array_push(v___x_5023_, v___x_5015_);
v___x_5025_ = lean_box(2);
v_decl_5026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5026_, 0, v___x_5025_);
lean_ctor_set(v_decl_5026_, 1, v___x_5021_);
lean_ctor_set(v_decl_5026_, 2, v___x_5024_);
v___x_5027_ = lean_box(0);
v___x_5028_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5028_, 0, v___x_5027_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1, v___x_5017_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1 + 1, v___x_5017_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1 + 2, v___x_5017_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1 + 3, v___x_5017_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*1 + 4, v___x_5017_);
v___x_5029_ = lean_box(2);
lean_inc_ref(v_decl_5026_);
v___x_5030_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5028_, v___x_5029_, v_decl_5026_, v_decl_5026_, v_dec_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_);
return v___x_5030_;
}
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; uint8_t v___x_5033_; 
v___x_5031_ = l_Lean_Syntax_getArg(v___x_5015_, v___x_5014_);
v___x_5032_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5031_);
v___x_5033_ = l_Lean_Syntax_isOfKind(v___x_5031_, v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; 
lean_dec(v___x_5031_);
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5034_;
}
else
{
lean_object* v___x_5035_; lean_object* v_xType_x3f_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v___x_5035_ = l_Lean_Syntax_getArg(v___x_5031_, v___x_5014_);
lean_dec(v___x_5031_);
v___x_5064_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5035_);
v___x_5065_ = l_Lean_Syntax_isOfKind(v___x_5035_, v___x_5064_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; 
lean_dec(v___x_5035_);
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; 
v___x_5067_ = lean_unsigned_to_nat(1u);
v___x_5068_ = l_Lean_Syntax_getArg(v___x_5015_, v___x_5067_);
v___x_5069_ = l_Lean_Syntax_matchesNull(v___x_5068_, v___x_5014_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; 
lean_dec(v___x_5035_);
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5070_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5070_;
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; 
v___x_5071_ = lean_unsigned_to_nat(2u);
v___x_5072_ = l_Lean_Syntax_getArg(v___x_5015_, v___x_5071_);
v___x_5073_ = l_Lean_Syntax_isNone(v___x_5072_);
if (v___x_5073_ == 0)
{
uint8_t v___x_5074_; 
lean_inc(v___x_5072_);
v___x_5074_ = l_Lean_Syntax_matchesNull(v___x_5072_, v___x_5067_);
if (v___x_5074_ == 0)
{
lean_object* v___x_5075_; 
lean_dec(v___x_5072_);
lean_dec(v___x_5035_);
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5075_;
}
else
{
lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; 
v___x_5076_ = l_Lean_Syntax_getArg(v___x_5072_, v___x_5014_);
lean_dec(v___x_5072_);
v___x_5077_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5076_);
v___x_5078_ = l_Lean_Syntax_isOfKind(v___x_5076_, v___x_5077_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; 
lean_dec(v___x_5076_);
lean_dec(v___x_5035_);
lean_dec(v___x_5015_);
lean_dec_ref(v_dec_4969_);
v___x_5079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5079_;
}
else
{
lean_object* v_xType_x3f_5080_; lean_object* v___x_5081_; 
v_xType_x3f_5080_ = l_Lean_Syntax_getArg(v___x_5076_, v___x_5067_);
lean_dec(v___x_5076_);
v___x_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5081_, 0, v_xType_x3f_5080_);
v_xType_x3f_5037_ = v___x_5081_;
v___y_5038_ = v_a_4970_;
v___y_5039_ = v_a_4971_;
v___y_5040_ = v_a_4972_;
v___y_5041_ = v_a_4973_;
v___y_5042_ = v_a_4974_;
v___y_5043_ = v_a_4975_;
v___y_5044_ = v_a_4976_;
goto v___jp_5036_;
}
}
}
else
{
lean_object* v___x_5082_; 
lean_dec(v___x_5072_);
v___x_5082_ = lean_box(0);
v_xType_x3f_5037_ = v___x_5082_;
v___y_5038_ = v_a_4970_;
v___y_5039_ = v_a_4971_;
v___y_5040_ = v_a_4972_;
v___y_5041_ = v_a_4973_;
v___y_5042_ = v_a_4974_;
v___y_5043_ = v_a_4975_;
v___y_5044_ = v_a_4976_;
goto v___jp_5036_;
}
}
}
v___jp_5036_:
{
lean_object* v_ref_5045_; lean_object* v___x_5046_; lean_object* v_tk_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; uint8_t v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_ref_5045_ = lean_ctor_get(v___y_5043_, 5);
v___x_5046_ = lean_unsigned_to_nat(3u);
v_tk_5047_ = l_Lean_Syntax_getArg(v___x_5015_, v___x_5046_);
v___x_5048_ = lean_unsigned_to_nat(4u);
v___x_5049_ = l_Lean_Syntax_getArg(v___x_5015_, v___x_5048_);
lean_dec(v___x_5015_);
v___x_5050_ = 0;
v___x_5051_ = l_Lean_SourceInfo_fromRef(v_ref_5045_, v___x_5050_);
v___x_5052_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5051_, 2);
v___x_5053_ = l_Lean_Syntax_node1(v___x_5051_, v___x_5032_, v___x_5035_);
v___x_5054_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5055_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5051_);
lean_ctor_set(v___x_5056_, 1, v___x_5054_);
lean_ctor_set(v___x_5056_, 2, v___x_5055_);
if (lean_obj_tag(v_xType_x3f_5037_) == 1)
{
lean_object* v_val_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_val_5057_ = lean_ctor_get(v_xType_x3f_5037_, 0);
lean_inc(v_val_5057_);
lean_dec_ref_known(v_xType_x3f_5037_, 1);
v___x_5058_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5059_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5051_, 2);
v___x_5060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5051_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
v___x_5061_ = l_Lean_Syntax_node2(v___x_5051_, v___x_5058_, v___x_5060_, v_val_5057_);
v___x_5062_ = l_Array_mkArray1___redArg(v___x_5061_);
v___y_4979_ = v___y_5043_;
v___y_4980_ = v___x_5049_;
v___y_4981_ = v___x_5053_;
v___y_4982_ = v___y_5041_;
v___y_4983_ = v___x_5051_;
v___y_4984_ = v___x_5050_;
v___y_4985_ = v___y_5044_;
v___y_4986_ = v___y_5038_;
v___y_4987_ = v___y_5042_;
v___y_4988_ = v___x_5054_;
v___y_4989_ = v___y_5039_;
v___y_4990_ = v___x_5052_;
v___y_4991_ = v___x_5056_;
v___y_4992_ = v___x_5055_;
v___y_4993_ = v_tk_5047_;
v___y_4994_ = v___y_5040_;
v___y_4995_ = v___x_5062_;
goto v___jp_4978_;
}
else
{
lean_object* v___x_5063_; 
lean_dec(v_xType_x3f_5037_);
v___x_5063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4979_ = v___y_5043_;
v___y_4980_ = v___x_5049_;
v___y_4981_ = v___x_5053_;
v___y_4982_ = v___y_5041_;
v___y_4983_ = v___x_5051_;
v___y_4984_ = v___x_5050_;
v___y_4985_ = v___y_5044_;
v___y_4986_ = v___y_5038_;
v___y_4987_ = v___y_5042_;
v___y_4988_ = v___x_5054_;
v___y_4989_ = v___y_5039_;
v___y_4990_ = v___x_5052_;
v___y_4991_ = v___x_5056_;
v___y_4992_ = v___x_5055_;
v___y_4993_ = v_tk_5047_;
v___y_4994_ = v___y_5040_;
v___y_4995_ = v___x_5063_;
goto v___jp_4978_;
}
}
}
}
}
v___jp_4978_:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_inc_ref(v___y_4992_);
v___x_4996_ = l_Array_append___redArg(v___y_4992_, v___y_4995_);
lean_dec_ref(v___y_4995_);
lean_inc(v___y_4988_);
lean_inc_n(v___y_4983_, 2);
v___x_4997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4997_, 0, v___y_4983_);
lean_ctor_set(v___x_4997_, 1, v___y_4988_);
lean_ctor_set(v___x_4997_, 2, v___x_4996_);
v___x_4998_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___y_4983_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
lean_inc(v___y_4990_);
v___x_5000_ = l_Lean_Syntax_node5(v___y_4983_, v___y_4990_, v___y_4981_, v___y_4991_, v___x_4997_, v___x_4999_, v___y_4980_);
v___x_5001_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5002_ = lean_unsigned_to_nat(1u);
v___x_5003_ = lean_mk_empty_array_with_capacity(v___x_5002_);
v___x_5004_ = lean_array_push(v___x_5003_, v___x_5000_);
v___x_5005_ = lean_box(2);
v___x_5006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
lean_ctor_set(v___x_5006_, 1, v___x_5001_);
lean_ctor_set(v___x_5006_, 2, v___x_5004_);
v___x_5007_ = lean_box(0);
v___x_5008_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
lean_ctor_set_uint8(v___x_5008_, sizeof(void*)*1, v___y_4984_);
lean_ctor_set_uint8(v___x_5008_, sizeof(void*)*1 + 1, v___y_4984_);
lean_ctor_set_uint8(v___x_5008_, sizeof(void*)*1 + 2, v___y_4984_);
lean_ctor_set_uint8(v___x_5008_, sizeof(void*)*1 + 3, v___y_4984_);
lean_ctor_set_uint8(v___x_5008_, sizeof(void*)*1 + 4, v___y_4984_);
v___x_5009_ = lean_box(2);
v___x_5010_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5008_, v___x_5009_, v___x_5006_, v___y_4993_, v_dec_4969_, v___y_4986_, v___y_4989_, v___y_4994_, v___y_4982_, v___y_4987_, v___y_4979_, v___y_4985_);
return v___x_5010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5083_, lean_object* v_dec_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5083_, v_dec_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_);
lean_dec(v_a_5091_);
lean_dec_ref(v_a_5090_);
lean_dec(v_a_5089_);
lean_dec_ref(v_a_5088_);
lean_dec(v_a_5087_);
lean_dec_ref(v_a_5086_);
lean_dec_ref(v_a_5085_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5101_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5102_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5103_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5104_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5105_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5101_, v___x_5102_, v___x_5103_, v___x_5104_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
uint8_t v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5117_ = 0;
v___x_5118_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5108_, v___x_5117_);
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5118_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v_____do__lift_5120_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5149_, size_t v_sz_5150_, size_t v_i_5151_, lean_object* v_b_5152_, lean_object* v___y_5153_){
_start:
{
uint8_t v___x_5155_; 
v___x_5155_ = lean_usize_dec_lt(v_i_5151_, v_sz_5150_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
v___x_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5156_, 0, v_b_5152_);
return v___x_5156_;
}
else
{
lean_object* v_ref_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v_a_5160_; uint8_t v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; size_t v___x_5194_; size_t v___x_5195_; 
v_ref_5157_ = lean_ctor_get(v___y_5153_, 5);
v___x_5158_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5160_ = lean_array_uget_borrowed(v_as_5149_, v_i_5151_);
v___x_5161_ = 0;
v___x_5162_ = l_Lean_SourceInfo_fromRef(v_ref_5157_, v___x_5161_);
v___x_5163_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5165_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5166_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5162_, 17);
v___x_5167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5162_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5162_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
v___x_5170_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5163_, v___x_5169_);
v___x_5171_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5162_);
lean_ctor_set(v___x_5172_, 1, v___x_5163_);
lean_ctor_set(v___x_5172_, 2, v___x_5171_);
lean_inc_ref_n(v___x_5172_, 3);
v___x_5173_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5158_, v___x_5172_);
v___x_5174_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5175_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5160_, 2);
v___x_5177_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5176_, v_a_5160_);
v___x_5178_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5162_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = l_Lean_Syntax_node5(v___x_5162_, v___x_5175_, v___x_5177_, v___x_5172_, v___x_5172_, v___x_5179_, v_a_5160_);
v___x_5181_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5174_, v___x_5180_);
v___x_5182_ = l_Lean_Syntax_node4(v___x_5162_, v___x_5165_, v___x_5167_, v___x_5170_, v___x_5173_, v___x_5181_);
v___x_5183_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5162_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5163_, v___x_5184_);
v___x_5186_ = l_Lean_Syntax_node2(v___x_5162_, v___x_5164_, v___x_5182_, v___x_5185_);
v___x_5187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5162_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
v___x_5190_ = l_Lean_Syntax_node2(v___x_5162_, v___x_5187_, v___x_5189_, v_b_5152_);
v___x_5191_ = l_Lean_Syntax_node2(v___x_5162_, v___x_5164_, v___x_5190_, v___x_5172_);
v___x_5192_ = l_Lean_Syntax_node2(v___x_5162_, v___x_5163_, v___x_5186_, v___x_5191_);
v___x_5193_ = l_Lean_Syntax_node1(v___x_5162_, v___x_5159_, v___x_5192_);
v___x_5194_ = ((size_t)1ULL);
v___x_5195_ = lean_usize_add(v_i_5151_, v___x_5194_);
v_i_5151_ = v___x_5195_;
v_b_5152_ = v___x_5193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5197_, lean_object* v_sz_5198_, lean_object* v_i_5199_, lean_object* v_b_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
size_t v_sz_boxed_5203_; size_t v_i_boxed_5204_; lean_object* v_res_5205_; 
v_sz_boxed_5203_ = lean_unbox_usize(v_sz_5198_);
lean_dec(v_sz_5198_);
v_i_boxed_5204_ = lean_unbox_usize(v_i_5199_);
lean_dec(v_i_5199_);
v_res_5205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5197_, v_sz_boxed_5203_, v_i_boxed_5204_, v_b_5200_, v___y_5201_);
lean_dec_ref(v___y_5201_);
lean_dec_ref(v_as_5197_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5206_, size_t v_sz_5207_, size_t v_i_5208_, lean_object* v_b_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
uint8_t v___x_5218_; 
v___x_5218_ = lean_usize_dec_lt(v_i_5208_, v_sz_5207_);
if (v___x_5218_ == 0)
{
lean_object* v___x_5219_; 
v___x_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5219_, 0, v_b_5209_);
return v___x_5219_;
}
else
{
lean_object* v_ref_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v_a_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; size_t v___x_5257_; size_t v___x_5258_; lean_object* v___x_5259_; 
v_ref_5220_ = lean_ctor_get(v___y_5215_, 5);
v___x_5221_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5223_ = lean_array_uget_borrowed(v_as_5206_, v_i_5208_);
v___x_5224_ = 0;
v___x_5225_ = l_Lean_SourceInfo_fromRef(v_ref_5220_, v___x_5224_);
v___x_5226_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5228_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5229_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5225_, 17);
v___x_5230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5225_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
v___x_5231_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5225_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5226_, v___x_5232_);
v___x_5234_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5225_);
lean_ctor_set(v___x_5235_, 1, v___x_5226_);
lean_ctor_set(v___x_5235_, 2, v___x_5234_);
lean_inc_ref_n(v___x_5235_, 3);
v___x_5236_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5221_, v___x_5235_);
v___x_5237_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5238_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5239_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5223_, 2);
v___x_5240_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5239_, v_a_5223_);
v___x_5241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5225_);
lean_ctor_set(v___x_5242_, 1, v___x_5241_);
v___x_5243_ = l_Lean_Syntax_node5(v___x_5225_, v___x_5238_, v___x_5240_, v___x_5235_, v___x_5235_, v___x_5242_, v_a_5223_);
v___x_5244_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5237_, v___x_5243_);
v___x_5245_ = l_Lean_Syntax_node4(v___x_5225_, v___x_5228_, v___x_5230_, v___x_5233_, v___x_5236_, v___x_5244_);
v___x_5246_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5225_);
lean_ctor_set(v___x_5247_, 1, v___x_5246_);
v___x_5248_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5226_, v___x_5247_);
v___x_5249_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5227_, v___x_5245_, v___x_5248_);
v___x_5250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5225_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5250_, v___x_5252_, v_b_5209_);
v___x_5254_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5227_, v___x_5253_, v___x_5235_);
v___x_5255_ = l_Lean_Syntax_node2(v___x_5225_, v___x_5226_, v___x_5249_, v___x_5254_);
v___x_5256_ = l_Lean_Syntax_node1(v___x_5225_, v___x_5222_, v___x_5255_);
v___x_5257_ = ((size_t)1ULL);
v___x_5258_ = lean_usize_add(v_i_5208_, v___x_5257_);
v___x_5259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5206_, v_sz_5207_, v___x_5258_, v___x_5256_, v___y_5215_);
return v___x_5259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5260_, lean_object* v_sz_5261_, lean_object* v_i_5262_, lean_object* v_b_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
size_t v_sz_boxed_5272_; size_t v_i_boxed_5273_; lean_object* v_res_5274_; 
v_sz_boxed_5272_ = lean_unbox_usize(v_sz_5261_);
lean_dec(v_sz_5261_);
v_i_boxed_5273_ = lean_unbox_usize(v_i_5262_);
lean_dec(v_i_5262_);
v_res_5274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5260_, v_sz_boxed_5272_, v_i_boxed_5273_, v_b_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec_ref(v_as_5260_);
return v_res_5274_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5314_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5315_ = l_String_toRawSubstring_x27(v___x_5314_);
return v___x_5315_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5329_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5330_ = l_String_toRawSubstring_x27(v___x_5329_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5347_, lean_object* v_dec_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_){
_start:
{
lean_object* v___x_5357_; uint8_t v___x_5358_; 
v___x_5357_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5347_);
v___x_5358_ = l_Lean_Syntax_isOfKind(v_stx_5347_, v___x_5357_);
if (v___x_5358_ == 0)
{
lean_object* v___x_5359_; 
lean_dec_ref(v_dec_5348_);
lean_dec(v_stx_5347_);
v___x_5359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5359_;
}
else
{
lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v___y_5363_; uint8_t v___y_5364_; lean_object* v___y_5365_; lean_object* v_body_5366_; lean_object* v___y_5367_; lean_object* v___y_5368_; lean_object* v___y_5369_; lean_object* v___y_5370_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5447_; lean_object* v___y_5448_; uint8_t v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; uint8_t v___y_5460_; lean_object* v___y_5461_; lean_object* v_a_5462_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; uint8_t v___y_5488_; lean_object* v___y_5489_; lean_object* v_mutTk_x3f_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___x_5592_; lean_object* v___x_5593_; uint8_t v___x_5594_; 
v___x_5592_ = lean_unsigned_to_nat(1u);
v___x_5593_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5592_);
v___x_5594_ = l_Lean_Syntax_isNone(v___x_5593_);
if (v___x_5594_ == 0)
{
uint8_t v___x_5595_; 
lean_inc(v___x_5593_);
v___x_5595_ = l_Lean_Syntax_matchesNull(v___x_5593_, v___x_5592_);
if (v___x_5595_ == 0)
{
lean_object* v___x_5596_; 
lean_dec(v___x_5593_);
lean_dec_ref(v_dec_5348_);
lean_dec(v_stx_5347_);
v___x_5596_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5596_;
}
else
{
lean_object* v___x_5597_; lean_object* v_mutTk_x3f_5598_; lean_object* v___x_5599_; 
v___x_5597_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5598_ = l_Lean_Syntax_getArg(v___x_5593_, v___x_5597_);
lean_dec(v___x_5593_);
v___x_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5599_, 0, v_mutTk_x3f_5598_);
v_mutTk_x3f_5561_ = v___x_5599_;
v___y_5562_ = v_a_5349_;
v___y_5563_ = v_a_5350_;
v___y_5564_ = v_a_5351_;
v___y_5565_ = v_a_5352_;
v___y_5566_ = v_a_5353_;
v___y_5567_ = v_a_5354_;
v___y_5568_ = v_a_5355_;
goto v___jp_5560_;
}
}
else
{
lean_object* v___x_5600_; 
lean_dec(v___x_5593_);
v___x_5600_ = lean_box(0);
v_mutTk_x3f_5561_ = v___x_5600_;
v___y_5562_ = v_a_5349_;
v___y_5563_ = v_a_5350_;
v___y_5564_ = v_a_5351_;
v___y_5565_ = v_a_5352_;
v___y_5566_ = v_a_5353_;
v___y_5567_ = v_a_5354_;
v___y_5568_ = v_a_5355_;
goto v___jp_5560_;
}
v___jp_5360_:
{
lean_object* v_eq_x3f_5374_; 
v_eq_x3f_5374_ = lean_ctor_get(v___y_5365_, 0);
lean_inc(v_eq_x3f_5374_);
lean_dec_ref(v___y_5365_);
if (lean_obj_tag(v_eq_x3f_5374_) == 1)
{
lean_object* v_val_5375_; lean_object* v_ref_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v_val_5375_ = lean_ctor_get(v_eq_x3f_5374_, 0);
lean_inc(v_val_5375_);
lean_dec_ref_known(v_eq_x3f_5374_, 1);
v_ref_5376_ = lean_ctor_get(v___y_5372_, 5);
v___x_5377_ = l_Lean_SourceInfo_fromRef(v_ref_5376_, v___y_5364_);
v___x_5378_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5379_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5377_, 19);
v___x_5380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5377_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
v___x_5381_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5382_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5377_);
lean_ctor_set(v___x_5383_, 1, v___x_5381_);
lean_ctor_set(v___x_5383_, 2, v___x_5382_);
v___x_5384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5385_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5377_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = l_Lean_Syntax_node2(v___x_5377_, v___x_5381_, v_val_5375_, v___x_5386_);
v___x_5388_ = l_Lean_Syntax_node2(v___x_5377_, v___x_5384_, v___x_5387_, v___y_5363_);
v___x_5389_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5381_, v___x_5388_);
v___x_5390_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5377_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
v___x_5392_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5377_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
v___x_5396_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5381_, v___y_5361_);
v___x_5397_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5381_, v___x_5396_);
v___x_5398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5377_);
lean_ctor_set(v___x_5399_, 1, v___x_5398_);
lean_inc_ref(v___x_5399_);
lean_inc_ref(v___x_5395_);
v___x_5400_ = l_Lean_Syntax_node4(v___x_5377_, v___x_5393_, v___x_5395_, v___x_5397_, v___x_5399_, v_body_5366_);
v___x_5401_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5402_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5403_, 0, v___x_5377_);
lean_ctor_set(v___x_5403_, 1, v___x_5402_);
v___x_5404_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5401_, v___x_5403_);
v___x_5405_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5381_, v___x_5404_);
v___x_5406_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5381_, v___x_5405_);
v___x_5407_ = l_Lean_Syntax_node4(v___x_5377_, v___x_5393_, v___x_5395_, v___x_5406_, v___x_5399_, v___y_5362_);
v___x_5408_ = l_Lean_Syntax_node2(v___x_5377_, v___x_5381_, v___x_5400_, v___x_5407_);
v___x_5409_ = l_Lean_Syntax_node1(v___x_5377_, v___x_5392_, v___x_5408_);
lean_inc_ref_n(v___x_5383_, 2);
v___x_5410_ = l_Lean_Syntax_node7(v___x_5377_, v___x_5378_, v___x_5380_, v___x_5383_, v___x_5383_, v___x_5383_, v___x_5389_, v___x_5391_, v___x_5409_);
v___x_5411_ = l_Lean_Elab_Do_elabDoElem(v___x_5410_, v_dec_5348_, v___x_5358_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
return v___x_5411_;
}
else
{
lean_object* v_ref_5412_; lean_object* v___x_5413_; lean_object* v_a_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
lean_dec(v_eq_x3f_5374_);
v_ref_5412_ = lean_ctor_get(v___y_5372_, 5);
v___x_5413_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5412_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc_n(v_a_5414_, 18);
lean_dec_ref(v___x_5413_);
v___x_5415_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5416_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5417_, 0, v_a_5414_);
lean_ctor_set(v___x_5417_, 1, v___x_5416_);
v___x_5418_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5419_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5420_, 0, v_a_5414_);
lean_ctor_set(v___x_5420_, 1, v___x_5418_);
lean_ctor_set(v___x_5420_, 2, v___x_5419_);
v___x_5421_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5420_, 3);
v___x_5422_ = l_Lean_Syntax_node2(v_a_5414_, v___x_5421_, v___x_5420_, v___y_5363_);
v___x_5423_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5418_, v___x_5422_);
v___x_5424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5425_, 0, v_a_5414_);
lean_ctor_set(v___x_5425_, 1, v___x_5424_);
v___x_5426_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5428_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5429_, 0, v_a_5414_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5418_, v___y_5361_);
v___x_5431_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5418_, v___x_5430_);
v___x_5432_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5433_, 0, v_a_5414_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
lean_inc_ref(v___x_5433_);
lean_inc_ref(v___x_5429_);
v___x_5434_ = l_Lean_Syntax_node4(v_a_5414_, v___x_5427_, v___x_5429_, v___x_5431_, v___x_5433_, v_body_5366_);
v___x_5435_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5436_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5437_, 0, v_a_5414_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5435_, v___x_5437_);
v___x_5439_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5418_, v___x_5438_);
v___x_5440_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5418_, v___x_5439_);
v___x_5441_ = l_Lean_Syntax_node4(v_a_5414_, v___x_5427_, v___x_5429_, v___x_5440_, v___x_5433_, v___y_5362_);
v___x_5442_ = l_Lean_Syntax_node2(v_a_5414_, v___x_5418_, v___x_5434_, v___x_5441_);
v___x_5443_ = l_Lean_Syntax_node1(v_a_5414_, v___x_5426_, v___x_5442_);
v___x_5444_ = l_Lean_Syntax_node7(v_a_5414_, v___x_5415_, v___x_5417_, v___x_5420_, v___x_5420_, v___x_5420_, v___x_5423_, v___x_5425_, v___x_5443_);
v___x_5445_ = l_Lean_Elab_Do_elabDoElem(v___x_5444_, v_dec_5348_, v___x_5358_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
return v___x_5445_;
}
}
v___jp_5446_:
{
if (lean_obj_tag(v___y_5452_) == 0)
{
lean_dec_ref(v___y_5451_);
v___y_5361_ = v___y_5454_;
v___y_5362_ = v___y_5455_;
v___y_5363_ = v___y_5456_;
v___y_5364_ = v___y_5449_;
v___y_5365_ = v___y_5461_;
v_body_5366_ = v_a_5462_;
v___y_5367_ = v___y_5459_;
v___y_5368_ = v___y_5457_;
v___y_5369_ = v___y_5448_;
v___y_5370_ = v___y_5450_;
v___y_5371_ = v___y_5453_;
v___y_5372_ = v___y_5458_;
v___y_5373_ = v___y_5447_;
goto v___jp_5360_;
}
else
{
lean_dec_ref_known(v___y_5452_, 1);
if (v___y_5460_ == 0)
{
lean_dec_ref(v___y_5451_);
v___y_5361_ = v___y_5454_;
v___y_5362_ = v___y_5455_;
v___y_5363_ = v___y_5456_;
v___y_5364_ = v___y_5449_;
v___y_5365_ = v___y_5461_;
v_body_5366_ = v_a_5462_;
v___y_5367_ = v___y_5459_;
v___y_5368_ = v___y_5457_;
v___y_5369_ = v___y_5448_;
v___y_5370_ = v___y_5450_;
v___y_5371_ = v___y_5453_;
v___y_5372_ = v___y_5458_;
v___y_5373_ = v___y_5447_;
goto v___jp_5360_;
}
else
{
size_t v_sz_5463_; size_t v___x_5464_; lean_object* v___x_5465_; 
v_sz_5463_ = lean_array_size(v___y_5451_);
v___x_5464_ = ((size_t)0ULL);
v___x_5465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5451_, v_sz_5463_, v___x_5464_, v_a_5462_, v___y_5459_, v___y_5457_, v___y_5448_, v___y_5450_, v___y_5453_, v___y_5458_, v___y_5447_);
lean_dec_ref(v___y_5451_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref_known(v___x_5465_, 1);
v___y_5361_ = v___y_5454_;
v___y_5362_ = v___y_5455_;
v___y_5363_ = v___y_5456_;
v___y_5364_ = v___y_5449_;
v___y_5365_ = v___y_5461_;
v_body_5366_ = v_a_5466_;
v___y_5367_ = v___y_5459_;
v___y_5368_ = v___y_5457_;
v___y_5369_ = v___y_5448_;
v___y_5370_ = v___y_5450_;
v___y_5371_ = v___y_5453_;
v___y_5372_ = v___y_5458_;
v___y_5373_ = v___y_5447_;
goto v___jp_5360_;
}
else
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5474_; 
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v_dec_5348_);
v_a_5467_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5469_ = v___x_5465_;
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5465_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5472_; 
if (v_isShared_5470_ == 0)
{
v___x_5472_ = v___x_5469_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
}
}
}
v___jp_5475_:
{
uint8_t v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5490_ = 0;
v___x_5491_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5492_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5485_, v___y_5479_, v___x_5491_, v___y_5484_, v___y_5477_, v___y_5478_, v___y_5480_, v___y_5486_, v___y_5476_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v___x_5492_, 1);
v___x_5494_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5493_, v___y_5487_, v___y_5484_, v___y_5477_, v___y_5478_, v___y_5480_, v___y_5486_, v___y_5476_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v___x_5495_; 
lean_dec_ref_known(v___x_5494_, 1);
lean_inc(v___y_5481_);
v___x_5495_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5481_, v___y_5484_, v___y_5477_, v___y_5478_, v___y_5480_, v___y_5486_, v___y_5476_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v___x_5495_, 1);
lean_inc(v___y_5479_);
v___x_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5497_, 0, v___y_5479_);
v___x_5498_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5497_, v_a_5496_, v___y_5487_, v___y_5484_, v___y_5477_, v___y_5478_, v___y_5480_, v___y_5486_, v___y_5476_);
lean_dec_ref_known(v___x_5497_, 1);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_dec_ref_known(v___x_5498_, 1);
if (lean_obj_tag(v___y_5489_) == 0)
{
lean_object* v_ref_5499_; lean_object* v_quotContext_5500_; lean_object* v_currMacroScope_5501_; lean_object* v___x_5502_; lean_object* v_a_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; 
v_ref_5499_ = lean_ctor_get(v___y_5486_, 5);
v_quotContext_5500_ = lean_ctor_get(v___y_5486_, 10);
v_currMacroScope_5501_ = lean_ctor_get(v___y_5486_, 11);
v___x_5502_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5499_, v___y_5487_, v___y_5484_, v___y_5477_, v___y_5478_, v___y_5480_, v___y_5486_, v___y_5476_);
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc_n(v_a_5503_, 9);
lean_dec_ref(v___x_5502_);
v___x_5504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5505_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5507_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5508_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5509_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5501_, 2);
lean_inc_n(v_quotContext_5500_, 2);
v___x_5511_ = l_Lean_addMacroScope(v_quotContext_5500_, v___x_5510_, v_currMacroScope_5501_);
v___x_5512_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5513_, 0, v_a_5503_);
lean_ctor_set(v___x_5513_, 1, v___x_5509_);
lean_ctor_set(v___x_5513_, 2, v___x_5511_);
lean_ctor_set(v___x_5513_, 3, v___x_5512_);
v___x_5514_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5516_ = l_Lean_addMacroScope(v_quotContext_5500_, v___x_5515_, v_currMacroScope_5501_);
v___x_5517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5518_, 0, v_a_5503_);
lean_ctor_set(v___x_5518_, 1, v___x_5514_);
lean_ctor_set(v___x_5518_, 2, v___x_5516_);
lean_ctor_set(v___x_5518_, 3, v___x_5517_);
v___x_5519_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5505_, v___x_5518_);
v___x_5520_ = l_Lean_Syntax_node2(v_a_5503_, v___x_5508_, v___x_5513_, v___x_5519_);
v___x_5521_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5507_, v___x_5520_);
v___x_5522_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5523_, 0, v_a_5503_);
lean_ctor_set(v___x_5523_, 1, v___x_5505_);
lean_ctor_set(v___x_5523_, 2, v___x_5522_);
v___x_5524_ = l_Lean_Syntax_node2(v_a_5503_, v___x_5506_, v___x_5521_, v___x_5523_);
v___x_5525_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5505_, v___x_5524_);
v___x_5526_ = l_Lean_Syntax_node1(v_a_5503_, v___x_5504_, v___x_5525_);
v___y_5447_ = v___y_5476_;
v___y_5448_ = v___y_5477_;
v___y_5449_ = v___x_5490_;
v___y_5450_ = v___y_5478_;
v___y_5451_ = v_a_5496_;
v___y_5452_ = v___y_5479_;
v___y_5453_ = v___y_5480_;
v___y_5454_ = v___y_5481_;
v___y_5455_ = v___y_5482_;
v___y_5456_ = v___y_5483_;
v___y_5457_ = v___y_5484_;
v___y_5458_ = v___y_5486_;
v___y_5459_ = v___y_5487_;
v___y_5460_ = v___y_5488_;
v___y_5461_ = v_a_5493_;
v_a_5462_ = v___x_5526_;
goto v___jp_5446_;
}
else
{
lean_object* v_val_5527_; 
v_val_5527_ = lean_ctor_get(v___y_5489_, 0);
lean_inc(v_val_5527_);
lean_dec_ref_known(v___y_5489_, 1);
v___y_5447_ = v___y_5476_;
v___y_5448_ = v___y_5477_;
v___y_5449_ = v___x_5490_;
v___y_5450_ = v___y_5478_;
v___y_5451_ = v_a_5496_;
v___y_5452_ = v___y_5479_;
v___y_5453_ = v___y_5480_;
v___y_5454_ = v___y_5481_;
v___y_5455_ = v___y_5482_;
v___y_5456_ = v___y_5483_;
v___y_5457_ = v___y_5484_;
v___y_5458_ = v___y_5486_;
v___y_5459_ = v___y_5487_;
v___y_5460_ = v___y_5488_;
v___y_5461_ = v_a_5493_;
v_a_5462_ = v_val_5527_;
goto v___jp_5446_;
}
}
else
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5535_; 
lean_dec(v_a_5496_);
lean_dec(v_a_5493_);
lean_dec(v___y_5489_);
lean_dec(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5348_);
v_a_5528_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5530_ = v___x_5498_;
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5498_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5528_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
lean_dec(v_a_5493_);
lean_dec(v___y_5489_);
lean_dec(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5348_);
v_a_5536_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5495_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5495_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
lean_dec(v_a_5493_);
lean_dec(v___y_5489_);
lean_dec(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5348_);
v_a_5544_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5494_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5494_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5559_; 
lean_dec(v___y_5489_);
lean_dec(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5348_);
v_a_5552_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5554_ = v___x_5492_;
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v___x_5492_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___x_5557_; 
if (v_isShared_5555_ == 0)
{
v___x_5557_ = v___x_5554_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
v___jp_5560_:
{
lean_object* v___x_5569_; lean_object* v_cfg_5570_; lean_object* v___x_5571_; uint8_t v___x_5572_; 
v___x_5569_ = lean_unsigned_to_nat(2u);
v_cfg_5570_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5569_);
v___x_5571_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5570_);
v___x_5572_ = l_Lean_Syntax_isOfKind(v_cfg_5570_, v___x_5571_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; 
lean_dec(v_cfg_5570_);
lean_dec(v_mutTk_x3f_5561_);
lean_dec_ref(v_dec_5348_);
lean_dec(v_stx_5347_);
v___x_5573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5573_;
}
else
{
lean_object* v___x_5574_; lean_object* v_pattern_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5574_ = lean_unsigned_to_nat(3u);
v_pattern_5575_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5574_);
v___x_5576_ = lean_unsigned_to_nat(5u);
v___x_5577_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5576_);
v___x_5578_ = lean_unsigned_to_nat(7u);
v___x_5579_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5578_);
v___x_5580_ = lean_unsigned_to_nat(8u);
v___x_5581_ = l_Lean_Syntax_getArg(v_stx_5347_, v___x_5580_);
lean_dec(v_stx_5347_);
v___x_5582_ = l_Lean_Syntax_getOptional_x3f(v___x_5581_);
lean_dec(v___x_5581_);
if (lean_obj_tag(v___x_5582_) == 0)
{
lean_object* v___x_5583_; 
v___x_5583_ = lean_box(0);
v___y_5476_ = v___y_5568_;
v___y_5477_ = v___y_5564_;
v___y_5478_ = v___y_5565_;
v___y_5479_ = v_mutTk_x3f_5561_;
v___y_5480_ = v___y_5566_;
v___y_5481_ = v_pattern_5575_;
v___y_5482_ = v___x_5579_;
v___y_5483_ = v___x_5577_;
v___y_5484_ = v___y_5563_;
v___y_5485_ = v_cfg_5570_;
v___y_5486_ = v___y_5567_;
v___y_5487_ = v___y_5562_;
v___y_5488_ = v___x_5572_;
v___y_5489_ = v___x_5583_;
goto v___jp_5475_;
}
else
{
lean_object* v_val_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
v_val_5584_ = lean_ctor_get(v___x_5582_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5582_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5586_ = v___x_5582_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_val_5584_);
lean_dec(v___x_5582_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_val_5584_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
v___y_5476_ = v___y_5568_;
v___y_5477_ = v___y_5564_;
v___y_5478_ = v___y_5565_;
v___y_5479_ = v_mutTk_x3f_5561_;
v___y_5480_ = v___y_5566_;
v___y_5481_ = v_pattern_5575_;
v___y_5482_ = v___x_5579_;
v___y_5483_ = v___x_5577_;
v___y_5484_ = v___y_5563_;
v___y_5485_ = v_cfg_5570_;
v___y_5486_ = v___y_5567_;
v___y_5487_ = v___y_5562_;
v___y_5488_ = v___x_5572_;
v___y_5489_ = v___x_5589_;
goto v___jp_5475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5601_, lean_object* v_dec_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5601_, v_dec_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
lean_dec(v_a_5607_);
lean_dec_ref(v_a_5606_);
lean_dec(v_a_5605_);
lean_dec_ref(v_a_5604_);
lean_dec_ref(v_a_5603_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5612_, size_t v_sz_5613_, size_t v_i_5614_, lean_object* v_b_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
lean_object* v___x_5624_; 
v___x_5624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5612_, v_sz_5613_, v_i_5614_, v_b_5615_, v___y_5621_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5625_, lean_object* v_sz_5626_, lean_object* v_i_5627_, lean_object* v_b_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
size_t v_sz_boxed_5637_; size_t v_i_boxed_5638_; lean_object* v_res_5639_; 
v_sz_boxed_5637_ = lean_unbox_usize(v_sz_5626_);
lean_dec(v_sz_5626_);
v_i_boxed_5638_ = lean_unbox_usize(v_i_5627_);
lean_dec(v_i_5627_);
v_res_5639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5625_, v_sz_boxed_5637_, v_i_boxed_5638_, v_b_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec_ref(v_as_5625_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5647_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5649_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5650_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5651_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5647_, v___x_5648_, v___x_5649_, v___x_5650_);
return v___x_5651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5653_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5661_; lean_object* v___x_5662_; 
v___x_5661_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5662_ = l_Lean_stringToMessageData(v___x_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5663_, lean_object* v_dec_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_){
_start:
{
lean_object* v___x_5673_; uint8_t v___x_5674_; 
v___x_5673_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5663_);
v___x_5674_ = l_Lean_Syntax_isOfKind(v_stx_5663_, v___x_5673_);
if (v___x_5674_ == 0)
{
lean_object* v___x_5675_; 
lean_dec_ref(v_dec_5664_);
lean_dec(v_stx_5663_);
v___x_5675_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5675_;
}
else
{
lean_object* v___x_5676_; lean_object* v_tk_5677_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; uint8_t v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___y_5723_; uint8_t v___y_5724_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; uint8_t v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; uint8_t v___y_5739_; lean_object* v_mutTk_x3f_5742_; lean_object* v___y_5743_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___x_5779_; lean_object* v___x_5780_; uint8_t v___x_5781_; 
v___x_5676_ = lean_unsigned_to_nat(0u);
v_tk_5677_ = l_Lean_Syntax_getArg(v_stx_5663_, v___x_5676_);
v___x_5779_ = lean_unsigned_to_nat(1u);
v___x_5780_ = l_Lean_Syntax_getArg(v_stx_5663_, v___x_5779_);
v___x_5781_ = l_Lean_Syntax_isNone(v___x_5780_);
if (v___x_5781_ == 0)
{
uint8_t v___x_5782_; 
lean_inc(v___x_5780_);
v___x_5782_ = l_Lean_Syntax_matchesNull(v___x_5780_, v___x_5779_);
if (v___x_5782_ == 0)
{
lean_object* v___x_5783_; 
lean_dec(v___x_5780_);
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
lean_dec(v_stx_5663_);
v___x_5783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5783_;
}
else
{
lean_object* v_mutTk_x3f_5784_; lean_object* v___x_5785_; 
v_mutTk_x3f_5784_ = l_Lean_Syntax_getArg(v___x_5780_, v___x_5676_);
lean_dec(v___x_5780_);
v___x_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5785_, 0, v_mutTk_x3f_5784_);
v_mutTk_x3f_5742_ = v___x_5785_;
v___y_5743_ = v_a_5665_;
v___y_5744_ = v_a_5666_;
v___y_5745_ = v_a_5667_;
v___y_5746_ = v_a_5668_;
v___y_5747_ = v_a_5669_;
v___y_5748_ = v_a_5670_;
v___y_5749_ = v_a_5671_;
goto v___jp_5741_;
}
}
else
{
lean_object* v___x_5786_; 
lean_dec(v___x_5780_);
v___x_5786_ = lean_box(0);
v_mutTk_x3f_5742_ = v___x_5786_;
v___y_5743_ = v_a_5665_;
v___y_5744_ = v_a_5666_;
v___y_5745_ = v_a_5667_;
v___y_5746_ = v_a_5668_;
v___y_5747_ = v_a_5669_;
v___y_5748_ = v_a_5670_;
v___y_5749_ = v_a_5671_;
goto v___jp_5741_;
}
v___jp_5678_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5688_, 0, v___y_5679_);
v___x_5689_ = l_Lean_Elab_Do_elabDoArrow(v___x_5688_, v___y_5680_, v_tk_5677_, v_dec_5664_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
lean_dec(v_tk_5677_);
return v___x_5689_;
}
v___jp_5690_:
{
lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5710_; 
lean_dec(v___y_5696_);
lean_dec(v___y_5692_);
v___x_5701_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5702_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5698_, v___x_5701_, v___y_5694_, v___y_5695_, v___y_5691_, v___y_5693_);
lean_dec(v___y_5698_);
v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5702_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5705_ = v___x_5702_;
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___x_5702_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5708_; 
if (v_isShared_5706_ == 0)
{
v___x_5708_ = v___x_5705_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_a_5703_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
v___jp_5711_:
{
if (v___y_5724_ == 0)
{
lean_object* v_eq_x3f_5725_; 
v_eq_x3f_5725_ = lean_ctor_get(v___y_5713_, 0);
lean_inc(v_eq_x3f_5725_);
lean_dec_ref(v___y_5713_);
if (lean_obj_tag(v_eq_x3f_5725_) == 0)
{
lean_dec(v___y_5723_);
v___y_5679_ = v___y_5719_;
v___y_5680_ = v___y_5722_;
v___y_5681_ = v___y_5721_;
v___y_5682_ = v___y_5716_;
v___y_5683_ = v___y_5717_;
v___y_5684_ = v___y_5718_;
v___y_5685_ = v___y_5715_;
v___y_5686_ = v___y_5712_;
v___y_5687_ = v___y_5714_;
goto v___jp_5678_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5725_, 1);
if (v___y_5720_ == 0)
{
lean_dec(v___y_5723_);
v___y_5679_ = v___y_5719_;
v___y_5680_ = v___y_5722_;
v___y_5681_ = v___y_5721_;
v___y_5682_ = v___y_5716_;
v___y_5683_ = v___y_5717_;
v___y_5684_ = v___y_5718_;
v___y_5685_ = v___y_5715_;
v___y_5686_ = v___y_5712_;
v___y_5687_ = v___y_5714_;
goto v___jp_5678_;
}
else
{
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
v___y_5691_ = v___y_5712_;
v___y_5692_ = v___y_5719_;
v___y_5693_ = v___y_5714_;
v___y_5694_ = v___y_5718_;
v___y_5695_ = v___y_5715_;
v___y_5696_ = v___y_5722_;
v___y_5697_ = v___y_5721_;
v___y_5698_ = v___y_5723_;
v___y_5699_ = v___y_5717_;
v___y_5700_ = v___y_5716_;
goto v___jp_5690_;
}
}
}
else
{
lean_dec_ref(v___y_5713_);
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
v___y_5691_ = v___y_5712_;
v___y_5692_ = v___y_5719_;
v___y_5693_ = v___y_5714_;
v___y_5694_ = v___y_5718_;
v___y_5695_ = v___y_5715_;
v___y_5696_ = v___y_5722_;
v___y_5697_ = v___y_5721_;
v___y_5698_ = v___y_5723_;
v___y_5699_ = v___y_5717_;
v___y_5700_ = v___y_5716_;
goto v___jp_5690_;
}
}
v___jp_5726_:
{
if (v___y_5739_ == 0)
{
uint8_t v_zeta_5740_; 
v_zeta_5740_ = lean_ctor_get_uint8(v___y_5728_, sizeof(void*)*1 + 2);
v___y_5712_ = v___y_5727_;
v___y_5713_ = v___y_5728_;
v___y_5714_ = v___y_5729_;
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5731_;
v___y_5717_ = v___y_5732_;
v___y_5718_ = v___y_5733_;
v___y_5719_ = v___y_5734_;
v___y_5720_ = v___y_5735_;
v___y_5721_ = v___y_5736_;
v___y_5722_ = v___y_5737_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v_zeta_5740_;
goto v___jp_5711_;
}
else
{
v___y_5712_ = v___y_5727_;
v___y_5713_ = v___y_5728_;
v___y_5714_ = v___y_5729_;
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5731_;
v___y_5717_ = v___y_5732_;
v___y_5718_ = v___y_5733_;
v___y_5719_ = v___y_5734_;
v___y_5720_ = v___y_5735_;
v___y_5721_ = v___y_5736_;
v___y_5722_ = v___y_5737_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___x_5674_;
goto v___jp_5711_;
}
}
v___jp_5741_:
{
lean_object* v___x_5750_; lean_object* v_cfg_5751_; lean_object* v___x_5752_; uint8_t v___x_5753_; 
v___x_5750_ = lean_unsigned_to_nat(2u);
v_cfg_5751_ = l_Lean_Syntax_getArg(v_stx_5663_, v___x_5750_);
v___x_5752_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5751_);
v___x_5753_ = l_Lean_Syntax_isOfKind(v_cfg_5751_, v___x_5752_);
if (v___x_5753_ == 0)
{
lean_object* v___x_5754_; 
lean_dec(v_cfg_5751_);
lean_dec(v_mutTk_x3f_5742_);
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
lean_dec(v_stx_5663_);
v___x_5754_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5754_;
}
else
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5755_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5751_);
v___x_5756_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5751_, v_mutTk_x3f_5742_, v___x_5755_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; lean_object* v___x_5758_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
lean_inc(v_a_5757_);
lean_dec_ref_known(v___x_5756_, 1);
v___x_5758_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5757_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
if (lean_obj_tag(v___x_5758_) == 0)
{
uint8_t v_nondep_5759_; uint8_t v_usedOnly_5760_; lean_object* v___x_5761_; lean_object* v_decl_5762_; 
lean_dec_ref_known(v___x_5758_, 1);
v_nondep_5759_ = lean_ctor_get_uint8(v_a_5757_, sizeof(void*)*1);
v_usedOnly_5760_ = lean_ctor_get_uint8(v_a_5757_, sizeof(void*)*1 + 1);
v___x_5761_ = lean_unsigned_to_nat(3u);
v_decl_5762_ = l_Lean_Syntax_getArg(v_stx_5663_, v___x_5761_);
lean_dec(v_stx_5663_);
if (v_nondep_5759_ == 0)
{
v___y_5727_ = v___y_5748_;
v___y_5728_ = v_a_5757_;
v___y_5729_ = v___y_5749_;
v___y_5730_ = v___y_5747_;
v___y_5731_ = v___y_5744_;
v___y_5732_ = v___y_5745_;
v___y_5733_ = v___y_5746_;
v___y_5734_ = v_mutTk_x3f_5742_;
v___y_5735_ = v___x_5753_;
v___y_5736_ = v___y_5743_;
v___y_5737_ = v_decl_5762_;
v___y_5738_ = v_cfg_5751_;
v___y_5739_ = v_usedOnly_5760_;
goto v___jp_5726_;
}
else
{
v___y_5727_ = v___y_5748_;
v___y_5728_ = v_a_5757_;
v___y_5729_ = v___y_5749_;
v___y_5730_ = v___y_5747_;
v___y_5731_ = v___y_5744_;
v___y_5732_ = v___y_5745_;
v___y_5733_ = v___y_5746_;
v___y_5734_ = v_mutTk_x3f_5742_;
v___y_5735_ = v___x_5753_;
v___y_5736_ = v___y_5743_;
v___y_5737_ = v_decl_5762_;
v___y_5738_ = v_cfg_5751_;
v___y_5739_ = v___x_5674_;
goto v___jp_5726_;
}
}
else
{
lean_object* v_a_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5770_; 
lean_dec(v_a_5757_);
lean_dec(v_cfg_5751_);
lean_dec(v_mutTk_x3f_5742_);
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
lean_dec(v_stx_5663_);
v_a_5763_ = lean_ctor_get(v___x_5758_, 0);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5758_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5765_ = v___x_5758_;
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_a_5763_);
lean_dec(v___x_5758_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5766_ == 0)
{
v___x_5768_ = v___x_5765_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
}
else
{
lean_object* v_a_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5778_; 
lean_dec(v_cfg_5751_);
lean_dec(v_mutTk_x3f_5742_);
lean_dec(v_tk_5677_);
lean_dec_ref(v_dec_5664_);
lean_dec(v_stx_5663_);
v_a_5771_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5773_ = v___x_5756_;
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_a_5771_);
lean_dec(v___x_5756_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5774_ == 0)
{
v___x_5776_ = v___x_5773_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5787_, lean_object* v_dec_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5787_, v_dec_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
lean_dec(v_a_5793_);
lean_dec_ref(v_a_5792_);
lean_dec(v_a_5791_);
lean_dec_ref(v_a_5790_);
lean_dec_ref(v_a_5789_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5805_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5806_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5807_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5808_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5809_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5805_, v___x_5806_, v___x_5807_, v___x_5808_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5818_, lean_object* v_dec_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_){
_start:
{
lean_object* v___x_5828_; uint8_t v___x_5829_; 
v___x_5828_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5818_);
v___x_5829_ = l_Lean_Syntax_isOfKind(v_stx_5818_, v___x_5828_);
if (v___x_5829_ == 0)
{
lean_object* v___x_5830_; 
lean_dec_ref(v_dec_5819_);
lean_dec(v_stx_5818_);
v___x_5830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5830_;
}
else
{
lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; uint8_t v___x_5834_; 
v___x_5831_ = lean_unsigned_to_nat(0u);
v___x_5832_ = l_Lean_Syntax_getArg(v_stx_5818_, v___x_5831_);
lean_dec(v_stx_5818_);
v___x_5833_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5832_);
v___x_5834_ = l_Lean_Syntax_isOfKind(v___x_5832_, v___x_5833_);
if (v___x_5834_ == 0)
{
lean_object* v___x_5835_; uint8_t v___x_5836_; 
v___x_5835_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5832_);
v___x_5836_ = l_Lean_Syntax_isOfKind(v___x_5832_, v___x_5835_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; 
lean_dec(v___x_5832_);
lean_dec_ref(v_dec_5819_);
v___x_5837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5837_;
}
else
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_box(2);
lean_inc(v___x_5832_);
v___x_5839_ = l_Lean_Elab_Do_elabDoArrow(v___x_5838_, v___x_5832_, v___x_5832_, v_dec_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_);
lean_dec(v___x_5832_);
return v___x_5839_;
}
}
else
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = lean_box(2);
lean_inc(v___x_5832_);
v___x_5841_ = l_Lean_Elab_Do_elabDoArrow(v___x_5840_, v___x_5832_, v___x_5832_, v_dec_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_);
lean_dec(v___x_5832_);
return v___x_5841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5842_, lean_object* v_dec_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_){
_start:
{
lean_object* v_res_5852_; 
v_res_5852_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5842_, v_dec_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_);
lean_dec(v_a_5850_);
lean_dec_ref(v_a_5849_);
lean_dec(v_a_5848_);
lean_dec_ref(v_a_5847_);
lean_dec(v_a_5846_);
lean_dec_ref(v_a_5845_);
lean_dec_ref(v_a_5844_);
return v_res_5852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5860_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5861_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5862_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5863_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5860_, v___x_5861_, v___x_5862_, v___x_5863_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5865_){
_start:
{
lean_object* v_res_5866_; 
v_res_5866_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5866_;
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
