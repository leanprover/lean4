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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_options_376_; lean_object* v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; 
v_options_376_ = lean_ctor_get(v___y_374_, 2);
v___x_377_ = l_Lean_Elab_pp_macroStack;
v___x_378_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_376_, v___x_377_);
v___x_379_ = lean_bool_not(v___x_378_);
if (v___x_379_ == 0)
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
else
{
lean_object* v___x_399_; 
lean_dec(v_macroStack_373_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_msgData_372_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_400_, lean_object* v_macroStack_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_400_, v_macroStack_401_, v___y_402_);
lean_dec_ref(v___y_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_ref_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v_macroStack_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_ref_413_ = lean_ctor_get(v___y_410_, 5);
v___x_414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_405_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v_macroStack_416_ = lean_ctor_get(v___y_406_, 1);
v___x_417_ = l_Lean_Elab_getBetterRef(v_ref_413_, v_macroStack_416_);
lean_inc(v_macroStack_416_);
v___x_418_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_415_, v_macroStack_416_, v___y_410_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_417_);
lean_ctor_set(v___x_423_, 1, v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 1);
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_436_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Array_mkArray0(lean_box(0));
return v___x_464_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_484_ = l_String_toRawSubstring_x27(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_531_, lean_object* v_decl_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
if (lean_obj_tag(v_letOrReassign_531_) == 2)
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_532_);
v___x_541_ = l_Lean_Syntax_isOfKind(v_decl_532_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_543_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_544_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l_Lean_Syntax_getArg(v_decl_532_, v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_547_);
v___x_549_ = l_Lean_Syntax_isOfKind(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___y_552_; lean_object* v_pattern_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___x_622_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_547_);
v___x_622_ = l_Lean_Syntax_isOfKind(v___x_547_, v___x_550_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_547_);
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_624_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_625_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = l_Lean_Syntax_getArg(v___x_547_, v___x_627_);
v___x_629_ = l_Lean_Syntax_matchesNull(v___x_628_, v___x_546_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_547_);
v___x_630_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_631_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_632_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_633_;
}
else
{
lean_object* v_pattern_634_; lean_object* v_xType_x3f_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_pattern_634_ = l_Lean_Syntax_getArg(v___x_547_, v___x_546_);
v___x_669_ = lean_unsigned_to_nat(2u);
v___x_670_ = l_Lean_Syntax_getArg(v___x_547_, v___x_669_);
v___x_671_ = l_Lean_Syntax_isNone(v___x_670_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
lean_inc(v___x_670_);
v___x_672_ = l_Lean_Syntax_matchesNull(v___x_670_, v___x_627_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_670_);
lean_dec(v_pattern_634_);
lean_dec(v___x_547_);
v___x_673_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_674_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_675_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = l_Lean_Syntax_getArg(v___x_670_, v___x_546_);
lean_dec(v___x_670_);
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_677_);
v___x_679_ = l_Lean_Syntax_isOfKind(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___x_677_);
lean_dec(v_pattern_634_);
lean_dec(v___x_547_);
v___x_680_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_681_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_682_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_683_;
}
else
{
lean_object* v_xType_x3f_684_; lean_object* v___x_685_; 
lean_dec(v_decl_532_);
v_xType_x3f_684_ = l_Lean_Syntax_getArg(v___x_677_, v___x_627_);
lean_dec(v___x_677_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_xType_x3f_684_);
v_xType_x3f_636_ = v___x_685_;
v___y_637_ = v_a_533_;
v___y_638_ = v_a_534_;
v___y_639_ = v_a_535_;
v___y_640_ = v_a_536_;
v___y_641_ = v_a_537_;
v___y_642_ = v_a_538_;
goto v___jp_635_;
}
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v___x_670_);
lean_dec(v_decl_532_);
v___x_686_ = lean_box(0);
v_xType_x3f_636_ = v___x_686_;
v___y_637_ = v_a_533_;
v___y_638_ = v_a_534_;
v___y_639_ = v_a_535_;
v___y_640_ = v_a_536_;
v___y_641_ = v_a_537_;
v___y_642_ = v_a_538_;
goto v___jp_635_;
}
v___jp_635_:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = l_Lean_Syntax_getArg(v___x_547_, v___x_643_);
lean_dec(v___x_547_);
if (lean_obj_tag(v_xType_x3f_636_) == 0)
{
v___y_552_ = v___x_644_;
v_pattern_553_ = v_pattern_634_;
v___y_554_ = v___y_637_;
v___y_555_ = v___y_638_;
v___y_556_ = v___y_639_;
v___y_557_ = v___y_640_;
v___y_558_ = v___y_641_;
v___y_559_ = v___y_642_;
goto v___jp_551_;
}
else
{
lean_object* v_val_645_; lean_object* v_ref_646_; lean_object* v_quotContext_647_; lean_object* v_currMacroScope_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_val_645_ = lean_ctor_get(v_xType_x3f_636_, 0);
lean_inc(v_val_645_);
lean_dec_ref_known(v_xType_x3f_636_, 1);
v_ref_646_ = lean_ctor_get(v___y_641_, 5);
v_quotContext_647_ = lean_ctor_get(v___y_641_, 10);
v_currMacroScope_648_ = lean_ctor_get(v___y_641_, 11);
v___x_649_ = l_Lean_SourceInfo_fromRef(v_ref_646_, v___x_549_);
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_649_, 7);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_649_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_655_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_656_ = lean_box(0);
lean_inc(v_currMacroScope_648_);
lean_inc(v_quotContext_647_);
v___x_657_ = l_Lean_addMacroScope(v_quotContext_647_, v___x_656_, v_currMacroScope_648_);
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_659_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_659_, 0, v___x_649_);
lean_ctor_set(v___x_659_, 1, v___x_655_);
lean_ctor_set(v___x_659_, 2, v___x_657_);
lean_ctor_set(v___x_659_, 3, v___x_658_);
v___x_660_ = l_Lean_Syntax_node1(v___x_649_, v___x_654_, v___x_659_);
v___x_661_ = l_Lean_Syntax_node2(v___x_649_, v___x_651_, v___x_653_, v___x_660_);
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_649_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_665_ = l_Lean_Syntax_node1(v___x_649_, v___x_664_, v_val_645_);
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_649_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_Syntax_node5(v___x_649_, v___x_650_, v___x_661_, v_pattern_634_, v___x_663_, v___x_665_, v___x_667_);
v___y_552_ = v___x_644_;
v_pattern_553_ = v___x_668_;
v___y_554_ = v___y_637_;
v___y_555_ = v___y_638_;
v___y_556_ = v___y_639_;
v___y_557_ = v___y_640_;
v___y_558_ = v___y_641_;
v___y_559_ = v___y_642_;
goto v___jp_551_;
}
}
}
}
v___jp_551_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_box(v___x_541_);
v___x_562_ = lean_box(v___x_541_);
lean_inc(v_pattern_553_);
v___x_563_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_563_, 0, v_pattern_553_);
lean_closure_set(v___x_563_, 1, v___x_560_);
lean_closure_set(v___x_563_, 2, v___x_561_);
lean_closure_set(v___x_563_, 3, v___x_562_);
v___x_564_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_563_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
v___x_566_ = lean_infer_type(v_a_565_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = l_Lean_Elab_Term_exprToSyntax(v_a_567_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_605_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_605_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_ref_573_; lean_object* v_quotContext_574_; lean_object* v_currMacroScope_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_ref_573_ = lean_ctor_get(v___y_558_, 5);
v_quotContext_574_ = lean_ctor_get(v___y_558_, 10);
v_currMacroScope_575_ = lean_ctor_get(v___y_558_, 11);
v___x_576_ = l_Lean_SourceInfo_fromRef(v_ref_573_, v___x_549_);
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
lean_inc(v_currMacroScope_575_);
lean_inc(v_quotContext_574_);
v___x_589_ = l_Lean_addMacroScope(v_quotContext_574_, v___x_588_, v_currMacroScope_575_);
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
v___x_599_ = l_Lean_Syntax_node5(v___x_576_, v___x_582_, v___x_593_, v___y_552_, v___x_595_, v___x_596_, v___x_598_);
lean_inc_ref(v___x_579_);
v___x_600_ = l_Lean_Syntax_node5(v___x_576_, v___x_550_, v_pattern_553_, v___x_579_, v___x_579_, v___x_581_, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v___x_576_, v___x_540_, v___x_600_);
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
lean_dec(v_pattern_553_);
lean_dec(v___y_552_);
return v___x_568_;
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_pattern_553_);
lean_dec(v___y_552_);
v_a_606_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_566_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_566_);
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
lean_dec(v_pattern_553_);
lean_dec(v___y_552_);
v_a_614_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_564_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_564_);
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
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = l_Lean_Syntax_getArg(v___x_547_, v___x_546_);
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_687_);
v___x_689_ = l_Lean_Syntax_isOfKind(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v___x_687_);
lean_dec(v___x_547_);
v___x_690_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_691_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_692_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_693_;
}
else
{
lean_object* v_x_694_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v_a_703_; lean_object* v_xType_x3f_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_x_694_ = l_Lean_Syntax_getArg(v___x_687_, v___x_546_);
lean_dec(v___x_687_);
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_694_);
v___x_781_ = l_Lean_Syntax_isOfKind(v_x_694_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_x_694_);
lean_dec(v___x_547_);
v___x_782_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_783_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_784_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = l_Lean_Syntax_getArg(v___x_547_, v___x_786_);
v___x_788_ = l_Lean_Syntax_matchesNull(v___x_787_, v___x_546_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v_x_694_);
lean_dec(v___x_547_);
v___x_789_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_790_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_791_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_unsigned_to_nat(2u);
v___x_794_ = l_Lean_Syntax_getArg(v___x_547_, v___x_793_);
v___x_795_ = l_Lean_Syntax_isNone(v___x_794_);
if (v___x_795_ == 0)
{
uint8_t v___x_796_; 
lean_inc(v___x_794_);
v___x_796_ = l_Lean_Syntax_matchesNull(v___x_794_, v___x_786_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v___x_794_);
lean_dec(v_x_694_);
lean_dec(v___x_547_);
v___x_797_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_798_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_799_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = l_Lean_Syntax_getArg(v___x_794_, v___x_546_);
lean_dec(v___x_794_);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_801_);
v___x_803_ = l_Lean_Syntax_isOfKind(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v___x_801_);
lean_dec(v_x_694_);
lean_dec(v___x_547_);
v___x_804_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_805_ = l_Lean_MessageData_ofSyntax(v_decl_532_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_806_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
return v___x_807_;
}
else
{
lean_object* v_xType_x3f_808_; lean_object* v___x_809_; 
lean_dec(v_decl_532_);
v_xType_x3f_808_ = l_Lean_Syntax_getArg(v___x_801_, v___x_786_);
lean_dec(v___x_801_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_xType_x3f_808_);
v_xType_x3f_752_ = v___x_809_;
v___y_753_ = v_a_533_;
v___y_754_ = v_a_534_;
v___y_755_ = v_a_535_;
v___y_756_ = v_a_536_;
v___y_757_ = v_a_537_;
v___y_758_ = v_a_538_;
goto v___jp_751_;
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec(v___x_794_);
lean_dec(v_decl_532_);
v___x_810_ = lean_box(0);
v_xType_x3f_752_ = v___x_810_;
v___y_753_ = v_a_533_;
v___y_754_ = v_a_534_;
v___y_755_ = v_a_535_;
v___y_756_ = v_a_536_;
v___y_757_ = v_a_537_;
v___y_758_ = v_a_538_;
goto v___jp_751_;
}
}
}
v___jp_695_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
lean_inc(v_x_694_);
v___x_705_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_694_, v_a_703_, v___x_541_, v___x_541_, v___x_704_, v___y_696_, v___y_702_, v___y_701_, v___y_699_, v___y_698_, v___y_700_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec_ref_known(v___x_705_, 1);
v___x_706_ = l_Lean_TSyntax_getId(v_x_694_);
v___x_707_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_706_, v___y_701_, v___y_699_, v___y_698_, v___y_700_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = l_Lean_LocalDecl_type(v_a_708_);
lean_dec(v_a_708_);
v___x_710_ = l_Lean_Elab_Term_exprToSyntax(v___x_709_, v___y_696_, v___y_702_, v___y_701_, v___y_699_, v___y_698_, v___y_700_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_734_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_734_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_734_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_734_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_ref_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v_ref_715_ = lean_ctor_get(v___y_698_, 5);
v___x_716_ = 0;
v___x_717_ = l_Lean_SourceInfo_fromRef(v_ref_715_, v___x_716_);
lean_inc_n(v___x_717_, 7);
v___x_718_ = l_Lean_Syntax_node1(v___x_717_, v___x_688_, v_x_694_);
v___x_719_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_721_, 0, v___x_717_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_717_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = l_Lean_Syntax_node2(v___x_717_, v___x_722_, v___x_724_, v_a_711_);
v___x_726_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_717_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_Syntax_node5(v___x_717_, v___x_548_, v___x_718_, v___x_721_, v___x_726_, v___x_728_, v___y_697_);
v___x_730_ = l_Lean_Syntax_node1(v___x_717_, v___x_540_, v___x_729_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_730_);
v___x_732_ = v___x_713_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_dec(v___y_697_);
lean_dec(v_x_694_);
return v___x_710_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___y_697_);
lean_dec(v_x_694_);
v_a_735_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_707_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_707_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v___y_697_);
lean_dec(v_x_694_);
v_a_743_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_705_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_705_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_751_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(4u);
v___x_760_ = l_Lean_Syntax_getArg(v___x_547_, v___x_759_);
lean_dec(v___x_547_);
if (lean_obj_tag(v_xType_x3f_752_) == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_box(0);
v___y_696_ = v___y_753_;
v___y_697_ = v___x_760_;
v___y_698_ = v___y_757_;
v___y_699_ = v___y_756_;
v___y_700_ = v___y_758_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_754_;
v_a_703_ = v___x_761_;
goto v___jp_695_;
}
else
{
lean_object* v_val_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_779_; 
v_val_762_ = lean_ctor_get(v_xType_x3f_752_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_xType_x3f_752_);
if (v_isSharedCheck_779_ == 0)
{
v___x_764_ = v_xType_x3f_752_;
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_val_762_);
lean_dec(v_xType_x3f_752_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Elab_Term_elabType(v_val_762_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_a_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
v___y_696_ = v___y_753_;
v___y_697_ = v___x_760_;
v___y_698_ = v___y_757_;
v___y_699_ = v___y_756_;
v___y_700_ = v___y_758_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_754_;
v_a_703_ = v___x_769_;
goto v___jp_695_;
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_764_);
lean_dec(v___x_760_);
lean_dec(v_x_694_);
v_a_771_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_766_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
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
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_decl_532_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_812_, lean_object* v_decl_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_812_, v_decl_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_letOrReassign_812_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_822_, lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_832_, lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_832_, v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_842_, lean_object* v_macroStack_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_842_, v_macroStack_843_, v___y_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_852_, lean_object* v_macroStack_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_852_, v_macroStack_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_ref_868_; lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_ref_868_ = lean_ctor_get(v___y_865_, 5);
v___x_869_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_inc(v_ref_868_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_ref_868_);
lean_ctor_set(v___x_874_, 1, v_a_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 1);
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_885_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
uint8_t v_postponeValue_901_; uint8_t v_generalize_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; 
v_postponeValue_901_ = lean_ctor_get_uint8(v_config_892_, sizeof(void*)*1 + 3);
v_generalize_902_ = lean_ctor_get_uint8(v_config_892_, sizeof(void*)*1 + 4);
if (v_postponeValue_901_ == 0)
{
v___y_904_ = v_a_893_;
v___y_905_ = v_a_894_;
v___y_906_ = v_a_895_;
v___y_907_ = v_a_896_;
v___y_908_ = v_a_897_;
v___y_909_ = v_a_898_;
v___y_910_ = v_a_899_;
goto v___jp_903_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_916_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_915_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
return v___x_916_;
}
v___jp_903_:
{
if (v_generalize_902_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_913_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_config_917_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_927_, lean_object* v_msg_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_928_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_938_, lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_938_, v_msg_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_keyedConfig_986_; uint8_t v_trackZetaDelta_987_; lean_object* v_zetaDeltaSet_988_; lean_object* v_localInstances_989_; lean_object* v_defEqCtx_x3f_990_; lean_object* v_synthPendingDepth_991_; lean_object* v_canUnfold_x3f_992_; uint8_t v_univApprox_993_; uint8_t v_inTypeClassResolution_994_; uint8_t v_cacheInferType_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_keyedConfig_986_ = lean_ctor_get(v___y_981_, 0);
v_trackZetaDelta_987_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*7);
v_zetaDeltaSet_988_ = lean_ctor_get(v___y_981_, 1);
v_localInstances_989_ = lean_ctor_get(v___y_981_, 3);
v_defEqCtx_x3f_990_ = lean_ctor_get(v___y_981_, 4);
v_synthPendingDepth_991_ = lean_ctor_get(v___y_981_, 5);
v_canUnfold_x3f_992_ = lean_ctor_get(v___y_981_, 6);
v_univApprox_993_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_994_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*7 + 2);
v_cacheInferType_995_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_992_);
lean_inc(v_synthPendingDepth_991_);
lean_inc(v_defEqCtx_x3f_990_);
lean_inc_ref(v_localInstances_989_);
lean_inc(v_zetaDeltaSet_988_);
lean_inc_ref(v_keyedConfig_986_);
v___x_996_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_996_, 0, v_keyedConfig_986_);
lean_ctor_set(v___x_996_, 1, v_zetaDeltaSet_988_);
lean_ctor_set(v___x_996_, 2, v_lctx_977_);
lean_ctor_set(v___x_996_, 3, v_localInstances_989_);
lean_ctor_set(v___x_996_, 4, v_defEqCtx_x3f_990_);
lean_ctor_set(v___x_996_, 5, v_synthPendingDepth_991_);
lean_ctor_set(v___x_996_, 6, v_canUnfold_x3f_992_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*7, v_trackZetaDelta_987_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*7 + 1, v_univApprox_993_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*7 + 2, v_inTypeClassResolution_994_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*7 + 3, v_cacheInferType_995_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v___y_982_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
v___x_997_ = lean_apply_7(v_x_978_, v___y_979_, v___y_980_, v___x_996_, v___y_982_, v___y_983_, v___y_984_, lean_box(0));
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1006_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1016_, lean_object* v_lctx_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_lctx_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1027_, v_lctx_1028_, v_x_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; 
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc_ref(v___y_1039_);
v___x_1048_ = lean_apply_9(v_k_1038_, v_b_1042_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, lean_box(0));
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1060_, lean_object* v_type_1061_, lean_object* v_val_1062_, lean_object* v_k_1063_, uint8_t v_nondep_1064_, uint8_t v_kind_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___f_1074_; lean_object* v___x_1075_; 
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc_ref(v___y_1066_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1074_, 0, v_k_1063_);
lean_closure_set(v___f_1074_, 1, v___y_1066_);
lean_closure_set(v___f_1074_, 2, v___y_1067_);
lean_closure_set(v___f_1074_, 3, v___y_1068_);
v___x_1075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1060_, v_type_1061_, v_val_1062_, v___f_1074_, v_nondep_1064_, v_kind_1065_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1075_) == 0)
{
return v___x_1075_;
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1084_, lean_object* v_type_1085_, lean_object* v_val_1086_, lean_object* v_k_1087_, lean_object* v_nondep_1088_, lean_object* v_kind_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_nondep_boxed_1098_; uint8_t v_kind_boxed_1099_; lean_object* v_res_1100_; 
v_nondep_boxed_1098_ = lean_unbox(v_nondep_1088_);
v_kind_boxed_1099_ = lean_unbox(v_kind_1089_);
v_res_1100_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1084_, v_type_1085_, v_val_1086_, v_k_1087_, v_nondep_boxed_1098_, v_kind_boxed_1099_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1101_, lean_object* v_name_1102_, lean_object* v_type_1103_, lean_object* v_val_1104_, lean_object* v_k_1105_, uint8_t v_nondep_1106_, uint8_t v_kind_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1102_, v_type_1103_, v_val_1104_, v_k_1105_, v_nondep_1106_, v_kind_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_name_1118_, lean_object* v_type_1119_, lean_object* v_val_1120_, lean_object* v_k_1121_, lean_object* v_nondep_1122_, lean_object* v_kind_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_nondep_boxed_1132_; uint8_t v_kind_boxed_1133_; lean_object* v_res_1134_; 
v_nondep_boxed_1132_ = lean_unbox(v_nondep_1122_);
v_kind_boxed_1133_ = lean_unbox(v_kind_1123_);
v_res_1134_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1117_, v_name_1118_, v_type_1119_, v_val_1120_, v_k_1121_, v_nondep_boxed_1132_, v_kind_boxed_1133_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1135_, lean_object* v___x_1136_, uint8_t v___x_1137_, lean_object* v___x_1138_, lean_object* v___x_1139_, uint8_t v___x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1135_, v___x_1136_, v___x_1137_, v___x_1137_, v___x_1138_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = 1;
v___x_1151_ = l_Lean_Meta_mkLambdaFVars(v___x_1139_, v_a_1149_, v___x_1140_, v___x_1140_, v___x_1140_, v___x_1137_, v___x_1150_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1151_;
}
else
{
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_98705__boxed_1165_; uint8_t v___x_98708__boxed_1166_; lean_object* v_res_1167_; 
v___x_98705__boxed_1165_ = lean_unbox(v___x_1154_);
v___x_98708__boxed_1166_ = lean_unbox(v___x_1157_);
v_res_1167_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1152_, v___x_1153_, v___x_98705__boxed_1165_, v___x_1155_, v___x_1156_, v___x_98708__boxed_1166_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___x_1156_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_ks_1172_; lean_object* v_vs_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1197_; 
v_ks_1172_ = lean_ctor_get(v_x_1168_, 0);
v_vs_1173_ = lean_ctor_get(v_x_1168_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1175_ = v_x_1168_;
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_vs_1173_);
lean_inc(v_ks_1172_);
lean_dec(v_x_1168_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = lean_array_get_size(v_ks_1172_);
v___x_1178_ = lean_nat_dec_lt(v_x_1169_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
lean_dec(v_x_1169_);
v___x_1179_ = lean_array_push(v_ks_1172_, v_x_1170_);
v___x_1180_ = lean_array_push(v_vs_1173_, v_x_1171_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1180_);
lean_ctor_set(v___x_1175_, 0, v___x_1179_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
else
{
lean_object* v_k_x27_1184_; uint8_t v___x_1185_; 
v_k_x27_1184_ = lean_array_fget_borrowed(v_ks_1172_, v_x_1169_);
v___x_1185_ = l_Lean_instBEqFVarId_beq(v_x_1170_, v_k_x27_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
if (v_isShared_1176_ == 0)
{
v___x_1187_ = v___x_1175_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_ks_1172_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_vs_1173_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_x_1169_, v___x_1188_);
lean_dec(v_x_1169_);
v_x_1168_ = v___x_1187_;
v_x_1169_ = v___x_1189_;
goto _start;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = lean_array_fset(v_ks_1172_, v_x_1169_, v_x_1170_);
v___x_1193_ = lean_array_fset(v_vs_1173_, v_x_1169_, v_x_1171_);
lean_dec(v_x_1169_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1193_);
lean_ctor_set(v___x_1175_, 0, v___x_1192_);
v___x_1195_ = v___x_1175_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1198_, lean_object* v_k_1199_, lean_object* v_v_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1198_, v___x_1201_, v_k_1199_, v_v_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1204_, size_t v_x_1205_, size_t v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
lean_object* v_es_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v_j_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_es_1209_ = lean_ctor_get(v_x_1204_, 0);
v___x_1210_ = ((size_t)31ULL);
v___x_1211_ = lean_usize_land(v_x_1205_, v___x_1210_);
v_j_1212_ = lean_usize_to_nat(v___x_1211_);
v___x_1213_ = lean_array_get_size(v_es_1209_);
v___x_1214_ = lean_nat_dec_lt(v_j_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_j_1212_);
lean_dec(v_x_1208_);
lean_dec(v_x_1207_);
return v_x_1204_;
}
else
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1253_; 
lean_inc_ref(v_es_1209_);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_x_1204_, 0);
lean_dec(v_unused_1254_);
v___x_1216_ = v_x_1204_;
v_isShared_1217_ = v_isSharedCheck_1253_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v_x_1204_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1253_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_v_1218_; lean_object* v___x_1219_; lean_object* v_xs_x27_1220_; lean_object* v___y_1222_; 
v_v_1218_ = lean_array_fget(v_es_1209_, v_j_1212_);
v___x_1219_ = lean_box(0);
v_xs_x27_1220_ = lean_array_fset(v_es_1209_, v_j_1212_, v___x_1219_);
switch(lean_obj_tag(v_v_1218_))
{
case 0:
{
lean_object* v_key_1227_; lean_object* v_val_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1238_; 
v_key_1227_ = lean_ctor_get(v_v_1218_, 0);
v_val_1228_ = lean_ctor_get(v_v_1218_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_v_1218_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1230_ = v_v_1218_;
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_val_1228_);
lean_inc(v_key_1227_);
lean_dec(v_v_1218_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
uint8_t v___x_1232_; 
v___x_1232_ = l_Lean_instBEqFVarId_beq(v_x_1207_, v_key_1227_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_del_object(v___x_1230_);
v___x_1233_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1227_, v_val_1228_, v_x_1207_, v_x_1208_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
v___y_1222_ = v___x_1234_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_val_1228_);
lean_dec(v_key_1227_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v_x_1208_);
lean_ctor_set(v___x_1230_, 0, v_x_1207_);
v___x_1236_ = v___x_1230_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_x_1207_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_x_1208_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
v___y_1222_ = v___x_1236_;
goto v___jp_1221_;
}
}
}
}
case 1:
{
lean_object* v_node_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1251_; 
v_node_1239_ = lean_ctor_get(v_v_1218_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_v_1218_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1241_ = v_v_1218_;
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_node_1239_);
lean_dec(v_v_1218_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_usize_shift_right(v_x_1205_, v___x_1243_);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_x_1206_, v___x_1245_);
v___x_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1239_, v___x_1244_, v___x_1246_, v_x_1207_, v_x_1208_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1247_);
v___x_1249_ = v___x_1241_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v___y_1222_ = v___x_1249_;
goto v___jp_1221_;
}
}
}
default: 
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_x_1207_);
lean_ctor_set(v___x_1252_, 1, v_x_1208_);
v___y_1222_ = v___x_1252_;
goto v___jp_1221_;
}
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_array_fset(v_xs_x27_1220_, v_j_1212_, v___y_1222_);
lean_dec(v_j_1212_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1223_);
v___x_1225_ = v___x_1216_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
else
{
lean_object* v_ks_1255_; lean_object* v_vs_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1276_; 
v_ks_1255_ = lean_ctor_get(v_x_1204_, 0);
v_vs_1256_ = lean_ctor_get(v_x_1204_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x_1204_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1258_ = v_x_1204_;
v_isShared_1259_ = v_isSharedCheck_1276_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_vs_1256_);
lean_inc(v_ks_1255_);
lean_dec(v_x_1204_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1276_;
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
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_ks_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_vs_1256_);
v___x_1261_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v_newNode_1262_; uint8_t v___y_1264_; size_t v___x_1270_; uint8_t v___x_1271_; 
v_newNode_1262_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1261_, v_x_1207_, v_x_1208_);
v___x_1270_ = ((size_t)7ULL);
v___x_1271_ = lean_usize_dec_le(v___x_1270_, v_x_1206_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1262_);
v___x_1273_ = lean_unsigned_to_nat(4u);
v___x_1274_ = lean_nat_dec_lt(v___x_1272_, v___x_1273_);
lean_dec(v___x_1272_);
v___y_1264_ = v___x_1274_;
goto v___jp_1263_;
}
else
{
v___y_1264_ = v___x_1271_;
goto v___jp_1263_;
}
v___jp_1263_:
{
if (v___y_1264_ == 0)
{
lean_object* v_ks_1265_; lean_object* v_vs_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_ks_1265_ = lean_ctor_get(v_newNode_1262_, 0);
lean_inc_ref(v_ks_1265_);
v_vs_1266_ = lean_ctor_get(v_newNode_1262_, 1);
lean_inc_ref(v_vs_1266_);
lean_dec_ref(v_newNode_1262_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1206_, v_ks_1265_, v_vs_1266_, v___x_1267_, v___x_1268_);
lean_dec_ref(v_vs_1266_);
lean_dec_ref(v_ks_1265_);
return v___x_1269_;
}
else
{
return v_newNode_1262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1277_, lean_object* v_keys_1278_, lean_object* v_vals_1279_, lean_object* v_i_1280_, lean_object* v_entries_1281_){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_array_get_size(v_keys_1278_);
v___x_1283_ = lean_nat_dec_lt(v_i_1280_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v_i_1280_);
return v_entries_1281_;
}
else
{
lean_object* v_k_1284_; lean_object* v_v_1285_; uint64_t v___x_1286_; size_t v_h_1287_; size_t v___x_1288_; lean_object* v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v_h_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_k_1284_ = lean_array_fget_borrowed(v_keys_1278_, v_i_1280_);
v_v_1285_ = lean_array_fget_borrowed(v_vals_1279_, v_i_1280_);
v___x_1286_ = l_Lean_instHashableFVarId_hash(v_k_1284_);
v_h_1287_ = lean_uint64_to_usize(v___x_1286_);
v___x_1288_ = ((size_t)5ULL);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = ((size_t)1ULL);
v___x_1291_ = lean_usize_sub(v_depth_1277_, v___x_1290_);
v___x_1292_ = lean_usize_mul(v___x_1288_, v___x_1291_);
v_h_1293_ = lean_usize_shift_right(v_h_1287_, v___x_1292_);
v___x_1294_ = lean_nat_add(v_i_1280_, v___x_1289_);
lean_dec(v_i_1280_);
lean_inc(v_v_1285_);
lean_inc(v_k_1284_);
v___x_1295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1281_, v_h_1293_, v_depth_1277_, v_k_1284_, v_v_1285_);
v_i_1280_ = v___x_1294_;
v_entries_1281_ = v___x_1295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1297_, lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_i_1300_, lean_object* v_entries_1301_){
_start:
{
size_t v_depth_boxed_1302_; lean_object* v_res_1303_; 
v_depth_boxed_1302_ = lean_unbox_usize(v_depth_1297_);
lean_dec(v_depth_1297_);
v_res_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1302_, v_keys_1298_, v_vals_1299_, v_i_1300_, v_entries_1301_);
lean_dec_ref(v_vals_1299_);
lean_dec_ref(v_keys_1298_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
size_t v_x_98828__boxed_1309_; size_t v_x_98829__boxed_1310_; lean_object* v_res_1311_; 
v_x_98828__boxed_1309_ = lean_unbox_usize(v_x_1305_);
lean_dec(v_x_1305_);
v_x_98829__boxed_1310_ = lean_unbox_usize(v_x_1306_);
lean_dec(v_x_1306_);
v_res_1311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1304_, v_x_98828__boxed_1309_, v_x_98829__boxed_1310_, v_x_1307_, v_x_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
uint64_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = l_Lean_instHashableFVarId_hash(v_x_1313_);
v___x_1316_ = lean_uint64_to_usize(v___x_1315_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1312_, v___x_1316_, v___x_1317_, v_x_1313_, v_x_1314_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_as_1319_, size_t v_i_1320_, size_t v_stop_1321_, lean_object* v_b_1322_){
_start:
{
lean_object* v___y_1324_; uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_eq(v_i_1320_, v_stop_1321_);
if (v___x_1328_ == 0)
{
lean_object* v_fvarIdToDecl_1329_; lean_object* v_decls_1330_; lean_object* v_auxDeclToFullName_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_fvarIdToDecl_1329_ = lean_ctor_get(v_b_1322_, 0);
v_decls_1330_ = lean_ctor_get(v_b_1322_, 1);
v_auxDeclToFullName_1331_ = lean_ctor_get(v_b_1322_, 2);
v___x_1332_ = lean_array_uget_borrowed(v_as_1319_, v_i_1320_);
v___x_1333_ = l_Lean_Expr_fvarId_x21(v___x_1332_);
lean_inc_ref(v_b_1322_);
v___x_1334_ = lean_local_ctx_find(v_b_1322_, v___x_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
v___y_1324_ = v_b_1322_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1361_; 
lean_inc(v_auxDeclToFullName_1331_);
lean_inc_ref(v_decls_1330_);
lean_inc_ref(v_fvarIdToDecl_1329_);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_b_1322_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; 
v_unused_1362_ = lean_ctor_get(v_b_1322_, 2);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_b_1322_, 1);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_b_1322_, 0);
lean_dec(v_unused_1364_);
v___x_1336_ = v_b_1322_;
v_isShared_1337_ = v_isSharedCheck_1361_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v_b_1322_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1361_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_val_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1360_; 
v_val_1338_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1340_ = v___x_1334_;
v_isShared_1341_ = v_isSharedCheck_1360_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_val_1338_);
lean_dec(v___x_1334_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1360_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1356_; lean_object* v_fvarId_1359_; 
v___x_1342_ = l_Lean_LocalDecl_type(v_val_1338_);
v___x_1343_ = l_Lean_Expr_cleanupAnnotations(v___x_1342_);
v___x_1344_ = l_Lean_LocalDecl_setType(v_val_1338_, v___x_1343_);
v_fvarId_1359_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_fvarId_1359_);
v___y_1356_ = v_fvarId_1359_;
goto v___jp_1355_;
v___jp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1344_);
v___x_1349_ = v___x_1340_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1344_);
v___x_1349_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lean_PersistentArray_set___redArg(v_decls_1330_, v___y_1347_, v___x_1349_);
lean_dec(v___y_1347_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v___x_1350_);
lean_ctor_set(v___x_1336_, 0, v___y_1346_);
v___x_1352_ = v___x_1336_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___y_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_auxDeclToFullName_1331_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
v___y_1324_ = v___x_1352_;
goto v___jp_1323_;
}
}
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v_index_1358_; 
lean_inc_ref(v___x_1344_);
v___x_1357_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1329_, v___y_1356_, v___x_1344_);
v_index_1358_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_index_1358_);
v___y_1346_ = v___x_1357_;
v___y_1347_ = v_index_1358_;
goto v___jp_1345_;
}
}
}
}
}
else
{
return v_b_1322_;
}
v___jp_1323_:
{
size_t v___x_1325_; size_t v___x_1326_; 
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1320_, v___x_1325_);
v_i_1320_ = v___x_1326_;
v_b_1322_ = v___y_1324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_as_1365_, lean_object* v_i_1366_, lean_object* v_stop_1367_, lean_object* v_b_1368_){
_start:
{
size_t v_i_boxed_1369_; size_t v_stop_boxed_1370_; lean_object* v_res_1371_; 
v_i_boxed_1369_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_stop_boxed_1370_ = lean_unbox_usize(v_stop_1367_);
lean_dec(v_stop_1367_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_as_1365_, v_i_boxed_1369_, v_stop_boxed_1370_, v_b_1368_);
lean_dec_ref(v_as_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(size_t v_sz_1372_, size_t v_i_1373_, lean_object* v_bs_1374_){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_usize_dec_lt(v_i_1373_, v_sz_1372_);
if (v___x_1375_ == 0)
{
return v_bs_1374_;
}
else
{
lean_object* v_v_1376_; lean_object* v_snd_1377_; lean_object* v___x_1378_; lean_object* v_bs_x27_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v_v_1376_ = lean_array_uget_borrowed(v_bs_1374_, v_i_1373_);
v_snd_1377_ = lean_ctor_get(v_v_1376_, 1);
lean_inc(v_snd_1377_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v_bs_x27_1379_ = lean_array_uset(v_bs_1374_, v_i_1373_, v___x_1378_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1373_, v___x_1380_);
v___x_1382_ = lean_array_uset(v_bs_x27_1379_, v_i_1373_, v_snd_1377_);
v_i_1373_ = v___x_1381_;
v_bs_1374_ = v___x_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_sz_1384_, lean_object* v_i_1385_, lean_object* v_bs_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1384_);
lean_dec(v_sz_1384_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1385_);
lean_dec(v_i_1385_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_boxed_1387_, v_i_boxed_1388_, v_bs_1386_);
return v_res_1389_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1392_ = l_Lean_stringToMessageData(v___x_1391_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1401_, lean_object* v_value_1402_, uint8_t v___x_1403_, uint8_t v___x_1404_, lean_object* v___x_1405_, uint8_t v___y_1406_, lean_object* v_xs_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
lean_inc(v_type_1401_);
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1415_, 0, v_type_1401_);
v___x_1416_ = 2;
v___x_1417_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1415_, v___x_1416_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; size_t v_sz_1419_; size_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___y_1423_; lean_object* v___y_1459_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v_sz_1419_ = lean_array_size(v_xs_1407_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_sz_1419_, v___x_1420_, v_xs_1407_);
if (v___y_1406_ == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1459_ = v___x_1495_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1459_ = v___x_1496_;
goto v___jp_1458_;
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
lean_inc(v_a_1418_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1418_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_box(v___x_1403_);
v___x_1427_ = lean_box(v___x_1404_);
lean_inc_ref(v___x_1421_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1428_, 0, v_value_1402_);
lean_closure_set(v___f_1428_, 1, v___x_1424_);
lean_closure_set(v___f_1428_, 2, v___x_1426_);
lean_closure_set(v___f_1428_, 3, v___x_1425_);
lean_closure_set(v___f_1428_, 4, v___x_1421_);
lean_closure_set(v___f_1428_, 5, v___x_1427_);
v___x_1429_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v___y_1423_, v___f_1428_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = 1;
v___x_1432_ = l_Lean_Meta_mkForallFVars(v___x_1421_, v_a_1418_, v___x_1404_, v___x_1403_, v___x_1403_, v___x_1431_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec_ref(v___x_1421_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1441_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1441_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1433_);
lean_ctor_set(v___x_1437_, 1, v_a_1430_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1430_);
v_a_1442_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1432_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1432_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
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
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___x_1421_);
lean_dec(v_a_1418_);
v_a_1450_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1429_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1429_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1460_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1459_);
v___x_1461_ = l_Lean_stringToMessageData(v___y_1459_);
lean_inc_ref(v___x_1461_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_inc(v_type_1401_);
v___x_1465_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1418_, v_type_1401_, v___x_1464_, v___y_1409_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref_known(v___x_1465_, 1);
v___x_1466_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1461_);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1463_);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_inc(v_a_1418_);
v___x_1470_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1418_, v_type_1401_, v___x_1469_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_lctx_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
lean_dec_ref_known(v___x_1470_, 1);
v_lctx_1471_ = lean_ctor_get(v___y_1410_, 2);
v___x_1472_ = lean_array_get_size(v___x_1421_);
v___x_1473_ = lean_nat_dec_lt(v___x_1405_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_inc_ref(v_lctx_1471_);
v___y_1423_ = v_lctx_1471_;
goto v___jp_1422_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_nat_dec_le(v___x_1472_, v___x_1472_);
if (v___x_1474_ == 0)
{
if (v___x_1473_ == 0)
{
lean_inc_ref(v_lctx_1471_);
v___y_1423_ = v_lctx_1471_;
goto v___jp_1422_;
}
else
{
size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_usize_of_nat(v___x_1472_);
lean_inc_ref(v_lctx_1471_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1421_, v___x_1420_, v___x_1475_, v_lctx_1471_);
v___y_1423_ = v___x_1476_;
goto v___jp_1422_;
}
}
else
{
size_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_usize_of_nat(v___x_1472_);
lean_inc_ref(v_lctx_1471_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v___x_1421_, v___x_1420_, v___x_1477_, v_lctx_1471_);
v___y_1423_ = v___x_1478_;
goto v___jp_1422_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v___x_1421_);
lean_dec(v_a_1418_);
lean_dec(v_value_1402_);
v_a_1479_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1470_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1470_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v___x_1461_);
lean_dec_ref(v___x_1421_);
lean_dec(v_a_1418_);
lean_dec(v_value_1402_);
lean_dec(v_type_1401_);
v_a_1487_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1465_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1465_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_xs_1407_);
lean_dec(v_value_1402_);
lean_dec(v_type_1401_);
v_a_1497_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1417_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1417_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1505_, lean_object* v_value_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, lean_object* v___x_1509_, lean_object* v___y_1510_, lean_object* v_xs_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v___x_99141__boxed_1519_; uint8_t v___x_99142__boxed_1520_; uint8_t v___y_99144__boxed_1521_; lean_object* v_res_1522_; 
v___x_99141__boxed_1519_ = lean_unbox(v___x_1507_);
v___x_99142__boxed_1520_ = lean_unbox(v___x_1508_);
v___y_99144__boxed_1521_ = lean_unbox(v___y_1510_);
v_res_1522_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1505_, v_value_1506_, v___x_99141__boxed_1519_, v___x_99142__boxed_1520_, v___x_1509_, v___y_99144__boxed_1521_, v_xs_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___x_1509_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1523_, lean_object* v_a_1524_, uint8_t v_zeta_1525_, uint8_t v___y_1526_, lean_object* v_x_1527_, uint8_t v_usedOnly_1528_, uint8_t v___x_1529_, uint8_t v___x_1530_, lean_object* v_snd_1531_, lean_object* v_h_x27_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
lean_inc_ref(v_h_x27_1532_);
v___x_1541_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1523_, v_h_x27_1532_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v___x_1541_, 1);
v___x_1542_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1524_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
if (v_zeta_1525_ == 0)
{
if (v___y_1526_ == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v_snd_1531_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_unsigned_to_nat(2u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1544_);
v___x_1546_ = lean_array_push(v___x_1545_, v_x_1527_);
v___x_1547_ = lean_array_push(v___x_1546_, v_h_x27_1532_);
v___x_1548_ = 1;
v___x_1549_ = l_Lean_Meta_mkLetFVars(v___x_1547_, v_a_1543_, v_usedOnly_1528_, v___x_1529_, v___x_1548_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
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
v___x_1553_ = lean_array_push(v___x_1552_, v_x_1527_);
v___x_1554_ = lean_array_push(v___x_1553_, v_h_x27_1532_);
v___x_1555_ = 1;
v___x_1556_ = l_Lean_Meta_mkLambdaFVars(v___x_1554_, v_a_1550_, v___x_1529_, v___x_1530_, v___x_1529_, v___x_1530_, v___x_1555_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
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
v___x_1571_ = lean_array_push(v___x_1570_, v_x_1527_);
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
lean_dec_ref(v_x_1527_);
return v___x_1542_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_h_x27_1532_);
lean_dec_ref(v_snd_1531_);
lean_dec_ref(v_x_1527_);
lean_dec_ref(v_a_1524_);
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
lean_object* v___x_1602_ = _args[7];
lean_object* v_snd_1603_ = _args[8];
lean_object* v_h_x27_1604_ = _args[9];
lean_object* v___y_1605_ = _args[10];
lean_object* v___y_1606_ = _args[11];
lean_object* v___y_1607_ = _args[12];
lean_object* v___y_1608_ = _args[13];
lean_object* v___y_1609_ = _args[14];
lean_object* v___y_1610_ = _args[15];
lean_object* v___y_1611_ = _args[16];
lean_object* v___y_1612_ = _args[17];
_start:
{
uint8_t v_zeta_boxed_1613_; uint8_t v___y_99368__boxed_1614_; uint8_t v_usedOnly_boxed_1615_; uint8_t v___x_99369__boxed_1616_; uint8_t v___x_99370__boxed_1617_; lean_object* v_res_1618_; 
v_zeta_boxed_1613_ = lean_unbox(v_zeta_1597_);
v___y_99368__boxed_1614_ = lean_unbox(v___y_1598_);
v_usedOnly_boxed_1615_ = lean_unbox(v_usedOnly_1600_);
v___x_99369__boxed_1616_ = lean_unbox(v___x_1601_);
v___x_99370__boxed_1617_ = lean_unbox(v___x_1602_);
v_res_1618_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1595_, v_a_1596_, v_zeta_boxed_1613_, v___y_99368__boxed_1614_, v_x_1599_, v_usedOnly_boxed_1615_, v___x_99369__boxed_1616_, v___x_99370__boxed_1617_, v_snd_1603_, v_h_x27_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1619_, lean_object* v_a_1620_, uint8_t v_zeta_1621_, lean_object* v_x_1622_, uint8_t v_usedOnly_1623_, uint8_t v___x_1624_, lean_object* v_snd_1625_, uint8_t v___y_1626_, uint8_t v___x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1619_) == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1620_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1636_) == 0)
{
if (v_zeta_1621_ == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v_snd_1625_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1638_);
v___x_1640_ = lean_array_push(v___x_1639_, v_x_1622_);
v___x_1641_ = 1;
v___x_1642_ = l_Lean_Meta_mkLetFVars(v___x_1640_, v_a_1637_, v_usedOnly_1623_, v___x_1624_, v___x_1641_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec_ref(v___x_1640_);
return v___x_1642_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_a_1643_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_mk_empty_array_with_capacity(v___x_1644_);
v___x_1646_ = lean_array_push(v___x_1645_, v_x_1622_);
v___x_1647_ = l_Lean_Expr_abstractM(v_a_1643_, v___x_1646_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec_ref(v___x_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_expr_instantiate1(v_a_1648_, v_snd_1625_);
lean_dec_ref(v_snd_1625_);
lean_dec(v_a_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_dec_ref(v_snd_1625_);
return v___x_1647_;
}
}
}
else
{
lean_dec_ref(v_snd_1625_);
lean_dec_ref(v_x_1622_);
return v___x_1636_;
}
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
v_val_1657_ = lean_ctor_get(v_eq_x3f_1619_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_eq_x3f_1619_, 1);
lean_inc_ref(v_snd_1625_);
lean_inc_ref(v_x_1622_);
v___x_1658_ = l_Lean_Meta_mkEq(v_x_1622_, v_snd_1625_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
lean_inc_ref(v_x_1622_);
v___x_1660_ = l_Lean_Meta_mkEqRefl(v_x_1622_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = lean_box(v_zeta_1621_);
v___x_1663_ = lean_box(v___y_1626_);
v___x_1664_ = lean_box(v_usedOnly_1623_);
v___x_1665_ = lean_box(v___x_1624_);
v___x_1666_ = lean_box(v___x_1627_);
lean_inc(v_val_1657_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1667_, 0, v_val_1657_);
lean_closure_set(v___f_1667_, 1, v_a_1620_);
lean_closure_set(v___f_1667_, 2, v___x_1662_);
lean_closure_set(v___f_1667_, 3, v___x_1663_);
lean_closure_set(v___f_1667_, 4, v_x_1622_);
lean_closure_set(v___f_1667_, 5, v___x_1664_);
lean_closure_set(v___f_1667_, 6, v___x_1665_);
lean_closure_set(v___f_1667_, 7, v___x_1666_);
lean_closure_set(v___f_1667_, 8, v_snd_1625_);
v___x_1668_ = l_Lean_TSyntax_getId(v_val_1657_);
lean_dec(v_val_1657_);
v___x_1669_ = 0;
v___x_1670_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1668_, v_a_1659_, v_a_1661_, v___f_1667_, v___x_1627_, v___x_1669_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1670_;
}
else
{
lean_dec(v_a_1659_);
lean_dec(v_val_1657_);
lean_dec_ref(v_snd_1625_);
lean_dec_ref(v_x_1622_);
lean_dec_ref(v_a_1620_);
return v___x_1660_;
}
}
else
{
lean_dec(v_val_1657_);
lean_dec_ref(v_snd_1625_);
lean_dec_ref(v_x_1622_);
lean_dec_ref(v_a_1620_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_eq_x3f_1671_ = _args[0];
lean_object* v_a_1672_ = _args[1];
lean_object* v_zeta_1673_ = _args[2];
lean_object* v_x_1674_ = _args[3];
lean_object* v_usedOnly_1675_ = _args[4];
lean_object* v___x_1676_ = _args[5];
lean_object* v_snd_1677_ = _args[6];
lean_object* v___y_1678_ = _args[7];
lean_object* v___x_1679_ = _args[8];
lean_object* v___y_1680_ = _args[9];
lean_object* v___y_1681_ = _args[10];
lean_object* v___y_1682_ = _args[11];
lean_object* v___y_1683_ = _args[12];
lean_object* v___y_1684_ = _args[13];
lean_object* v___y_1685_ = _args[14];
lean_object* v___y_1686_ = _args[15];
lean_object* v___y_1687_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1688_; uint8_t v_usedOnly_boxed_1689_; uint8_t v___x_99523__boxed_1690_; uint8_t v___y_99525__boxed_1691_; uint8_t v___x_99526__boxed_1692_; lean_object* v_res_1693_; 
v_zeta_boxed_1688_ = lean_unbox(v_zeta_1673_);
v_usedOnly_boxed_1689_ = lean_unbox(v_usedOnly_1675_);
v___x_99523__boxed_1690_ = lean_unbox(v___x_1676_);
v___y_99525__boxed_1691_ = lean_unbox(v___y_1678_);
v___x_99526__boxed_1692_ = lean_unbox(v___x_1679_);
v_res_1693_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1671_, v_a_1672_, v_zeta_boxed_1688_, v_x_1674_, v_usedOnly_boxed_1689_, v___x_99523__boxed_1690_, v_snd_1677_, v___y_99525__boxed_1691_, v___x_99526__boxed_1692_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1694_, lean_object* v_eq_x3f_1695_, lean_object* v_a_1696_, uint8_t v_zeta_1697_, uint8_t v_usedOnly_1698_, uint8_t v___x_1699_, lean_object* v_snd_1700_, uint8_t v___y_1701_, uint8_t v___x_1702_, lean_object* v_letOrReassign_1703_, lean_object* v_a_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
lean_inc_ref(v_x_1705_);
v___x_1714_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1694_, v_x_1705_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___y_1720_; lean_object* v___x_1721_; 
lean_dec_ref_known(v___x_1714_, 1);
v___x_1715_ = lean_box(v_zeta_1697_);
v___x_1716_ = lean_box(v_usedOnly_1698_);
v___x_1717_ = lean_box(v___x_1699_);
v___x_1718_ = lean_box(v___y_1701_);
v___x_1719_ = lean_box(v___x_1702_);
v___y_1720_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 17, 9);
lean_closure_set(v___y_1720_, 0, v_eq_x3f_1695_);
lean_closure_set(v___y_1720_, 1, v_a_1696_);
lean_closure_set(v___y_1720_, 2, v___x_1715_);
lean_closure_set(v___y_1720_, 3, v_x_1705_);
lean_closure_set(v___y_1720_, 4, v___x_1716_);
lean_closure_set(v___y_1720_, 5, v___x_1717_);
lean_closure_set(v___y_1720_, 6, v_snd_1700_);
lean_closure_set(v___y_1720_, 7, v___x_1718_);
lean_closure_set(v___y_1720_, 8, v___x_1719_);
v___x_1721_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1703_, v_a_1704_, v___y_1720_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1721_;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_x_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_letOrReassign_1703_);
lean_dec_ref(v_snd_1700_);
lean_dec_ref(v_a_1696_);
lean_dec(v_eq_x3f_1695_);
v_a_1722_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1714_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1714_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1730_ = _args[0];
lean_object* v_eq_x3f_1731_ = _args[1];
lean_object* v_a_1732_ = _args[2];
lean_object* v_zeta_1733_ = _args[3];
lean_object* v_usedOnly_1734_ = _args[4];
lean_object* v___x_1735_ = _args[5];
lean_object* v_snd_1736_ = _args[6];
lean_object* v___y_1737_ = _args[7];
lean_object* v___x_1738_ = _args[8];
lean_object* v_letOrReassign_1739_ = _args[9];
lean_object* v_a_1740_ = _args[10];
lean_object* v_x_1741_ = _args[11];
lean_object* v___y_1742_ = _args[12];
lean_object* v___y_1743_ = _args[13];
lean_object* v___y_1744_ = _args[14];
lean_object* v___y_1745_ = _args[15];
lean_object* v___y_1746_ = _args[16];
lean_object* v___y_1747_ = _args[17];
lean_object* v___y_1748_ = _args[18];
lean_object* v___y_1749_ = _args[19];
_start:
{
uint8_t v_zeta_boxed_1750_; uint8_t v_usedOnly_boxed_1751_; uint8_t v___x_99636__boxed_1752_; uint8_t v___y_99638__boxed_1753_; uint8_t v___x_99639__boxed_1754_; lean_object* v_res_1755_; 
v_zeta_boxed_1750_ = lean_unbox(v_zeta_1733_);
v_usedOnly_boxed_1751_ = lean_unbox(v_usedOnly_1734_);
v___x_99636__boxed_1752_ = lean_unbox(v___x_1735_);
v___y_99638__boxed_1753_ = lean_unbox(v___y_1737_);
v___x_99639__boxed_1754_ = lean_unbox(v___x_1738_);
v_res_1755_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1730_, v_eq_x3f_1731_, v_a_1732_, v_zeta_boxed_1750_, v_usedOnly_boxed_1751_, v___x_99636__boxed_1752_, v_snd_1736_, v___y_99638__boxed_1753_, v___x_99639__boxed_1754_, v_letOrReassign_1739_, v_a_1740_, v_x_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1756_, lean_object* v_____do__lift_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1757_, v___x_1756_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1768_, lean_object* v_____do__lift_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v___x_99710__boxed_1778_; lean_object* v_res_1779_; 
v___x_99710__boxed_1778_ = lean_unbox(v___x_1768_);
v_res_1779_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99710__boxed_1778_, v_____do__lift_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_____do__lift_1769_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1780_, lean_object* v___x_1781_, uint8_t v___x_1782_, lean_object* v___x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1780_, v___x_1781_, v___x_1782_, v___x_1782_, v___x_1783_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v___x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_99745__boxed_1805_; lean_object* v_res_1806_; 
v___x_99745__boxed_1805_ = lean_unbox(v___x_1795_);
v_res_1806_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1793_, v___x_1794_, v___x_99745__boxed_1805_, v___x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
lean_inc_ref(v___y_1808_);
v___x_1816_ = lean_apply_8(v_x_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, lean_box(0));
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec_ref(v___y_1818_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1827_, lean_object* v_mkInfoTree_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v_a_1834_, lean_object* v_a_x3f_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v_infoState_1838_; lean_object* v_trees_1839_; lean_object* v___x_1840_; 
v___x_1837_ = lean_st_ref_get(v___y_1827_);
v_infoState_1838_ = lean_ctor_get(v___x_1837_, 7);
lean_inc_ref(v_infoState_1838_);
lean_dec(v___x_1837_);
v_trees_1839_ = lean_ctor_get(v_infoState_1838_, 2);
lean_inc_ref(v_trees_1839_);
lean_dec_ref(v_infoState_1838_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_1840_ = lean_apply_8(v_mkInfoTree_1828_, v_trees_1839_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1827_, lean_box(0));
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1879_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1879_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1879_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v_infoState_1846_; lean_object* v_env_1847_; lean_object* v_nextMacroScope_1848_; lean_object* v_ngen_1849_; lean_object* v_auxDeclNGen_1850_; lean_object* v_traceState_1851_; lean_object* v_cache_1852_; lean_object* v_messages_1853_; lean_object* v_snapshotTasks_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1878_; 
v___x_1845_ = lean_st_ref_take(v___y_1827_);
v_infoState_1846_ = lean_ctor_get(v___x_1845_, 7);
v_env_1847_ = lean_ctor_get(v___x_1845_, 0);
v_nextMacroScope_1848_ = lean_ctor_get(v___x_1845_, 1);
v_ngen_1849_ = lean_ctor_get(v___x_1845_, 2);
v_auxDeclNGen_1850_ = lean_ctor_get(v___x_1845_, 3);
v_traceState_1851_ = lean_ctor_get(v___x_1845_, 4);
v_cache_1852_ = lean_ctor_get(v___x_1845_, 5);
v_messages_1853_ = lean_ctor_get(v___x_1845_, 6);
v_snapshotTasks_1854_ = lean_ctor_get(v___x_1845_, 8);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1856_ = v___x_1845_;
v_isShared_1857_ = v_isSharedCheck_1878_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_snapshotTasks_1854_);
lean_inc(v_infoState_1846_);
lean_inc(v_messages_1853_);
lean_inc(v_cache_1852_);
lean_inc(v_traceState_1851_);
lean_inc(v_auxDeclNGen_1850_);
lean_inc(v_ngen_1849_);
lean_inc(v_nextMacroScope_1848_);
lean_inc(v_env_1847_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1878_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
uint8_t v_enabled_1858_; lean_object* v_assignment_1859_; lean_object* v_lazyAssignment_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1876_; 
v_enabled_1858_ = lean_ctor_get_uint8(v_infoState_1846_, sizeof(void*)*3);
v_assignment_1859_ = lean_ctor_get(v_infoState_1846_, 0);
v_lazyAssignment_1860_ = lean_ctor_get(v_infoState_1846_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_infoState_1846_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v_infoState_1846_, 2);
lean_dec(v_unused_1877_);
v___x_1862_ = v_infoState_1846_;
v_isShared_1863_ = v_isSharedCheck_1876_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_lazyAssignment_1860_);
lean_inc(v_assignment_1859_);
lean_dec(v_infoState_1846_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1876_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1864_ = l_Lean_PersistentArray_push___redArg(v_a_1834_, v_a_1841_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 2, v___x_1864_);
v___x_1866_ = v___x_1862_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_assignment_1859_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_lazyAssignment_1860_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v___x_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1875_, sizeof(void*)*3, v_enabled_1858_);
v___x_1866_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 7, v___x_1866_);
v___x_1868_ = v___x_1856_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_env_1847_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1848_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1849_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1850_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_traceState_1851_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_cache_1852_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_messages_1853_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_snapshotTasks_1854_);
v___x_1868_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1869_ = lean_st_ref_set(v___y_1827_, v___x_1868_);
v___x_1870_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1870_);
v___x_1872_ = v___x_1843_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_a_1834_);
v_a_1880_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1840_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1840_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_1888_, lean_object* v_mkInfoTree_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v_a_1895_, lean_object* v_a_x3f_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1888_, v_mkInfoTree_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v_a_1895_, v_a_x3f_1896_);
lean_dec(v_a_x3f_1896_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1888_);
return v_res_1898_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_unsigned_to_nat(32u);
v___x_1900_ = lean_mk_empty_array_with_capacity(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1(void){
_start:
{
size_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = ((size_t)5ULL);
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_unsigned_to_nat(32u);
v___x_1905_ = lean_mk_empty_array_with_capacity(v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__0);
v___x_1907_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
lean_ctor_set(v___x_1907_, 2, v___x_1903_);
lean_ctor_set(v___x_1907_, 3, v___x_1903_);
lean_ctor_set_usize(v___x_1907_, 4, v___x_1902_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v_infoState_1911_; lean_object* v_trees_1912_; lean_object* v___x_1913_; lean_object* v_infoState_1914_; lean_object* v_env_1915_; lean_object* v_nextMacroScope_1916_; lean_object* v_ngen_1917_; lean_object* v_auxDeclNGen_1918_; lean_object* v_traceState_1919_; lean_object* v_cache_1920_; lean_object* v_messages_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1943_; 
v___x_1910_ = lean_st_ref_get(v___y_1908_);
v_infoState_1911_ = lean_ctor_get(v___x_1910_, 7);
lean_inc_ref(v_infoState_1911_);
lean_dec(v___x_1910_);
v_trees_1912_ = lean_ctor_get(v_infoState_1911_, 2);
lean_inc_ref(v_trees_1912_);
lean_dec_ref(v_infoState_1911_);
v___x_1913_ = lean_st_ref_take(v___y_1908_);
v_infoState_1914_ = lean_ctor_get(v___x_1913_, 7);
v_env_1915_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1916_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1917_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1918_ = lean_ctor_get(v___x_1913_, 3);
v_traceState_1919_ = lean_ctor_get(v___x_1913_, 4);
v_cache_1920_ = lean_ctor_get(v___x_1913_, 5);
v_messages_1921_ = lean_ctor_get(v___x_1913_, 6);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1913_, 8);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1943_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1914_);
lean_inc(v_messages_1921_);
lean_inc(v_cache_1920_);
lean_inc(v_traceState_1919_);
lean_inc(v_auxDeclNGen_1918_);
lean_inc(v_ngen_1917_);
lean_inc(v_nextMacroScope_1916_);
lean_inc(v_env_1915_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1943_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint8_t v_enabled_1926_; lean_object* v_assignment_1927_; lean_object* v_lazyAssignment_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1941_; 
v_enabled_1926_ = lean_ctor_get_uint8(v_infoState_1914_, sizeof(void*)*3);
v_assignment_1927_ = lean_ctor_get(v_infoState_1914_, 0);
v_lazyAssignment_1928_ = lean_ctor_get(v_infoState_1914_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_infoState_1914_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_infoState_1914_, 2);
lean_dec(v_unused_1942_);
v___x_1930_ = v_infoState_1914_;
v_isShared_1931_ = v_isSharedCheck_1941_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_lazyAssignment_1928_);
lean_inc(v_assignment_1927_);
lean_dec(v_infoState_1914_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1941_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___closed__1);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 2, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_assignment_1927_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_lazyAssignment_1928_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v___x_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1940_, sizeof(void*)*3, v_enabled_1926_);
v___x_1934_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 7, v___x_1934_);
v___x_1936_ = v___x_1924_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_env_1915_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_nextMacroScope_1916_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_ngen_1917_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_auxDeclNGen_1918_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_traceState_1919_);
lean_ctor_set(v_reuseFailAlloc_1939_, 5, v_cache_1920_);
lean_ctor_set(v_reuseFailAlloc_1939_, 6, v_messages_1921_);
lean_ctor_set(v_reuseFailAlloc_1939_, 7, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1939_, 8, v_snapshotTasks_1922_);
v___x_1936_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_st_ref_set(v___y_1908_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_trees_1912_);
return v___x_1938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1944_);
lean_dec(v___y_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_1947_, lean_object* v_mkInfoTree_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_infoState_1957_; uint8_t v_enabled_1958_; 
v___x_1956_ = lean_st_ref_get(v___y_1954_);
v_infoState_1957_ = lean_ctor_get(v___x_1956_, 7);
lean_inc_ref(v_infoState_1957_);
lean_dec(v___x_1956_);
v_enabled_1958_ = lean_ctor_get_uint8(v_infoState_1957_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1957_);
if (v_enabled_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_mkInfoTree_1948_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
v___x_1959_ = lean_apply_7(v_x_1947_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v_r_1962_; 
v___x_1960_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_1954_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
v_r_1962_ = lean_apply_7(v_x_1947_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
if (lean_obj_tag(v_r_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1987_; 
v_a_1963_ = lean_ctor_get(v_r_1962_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_r_1962_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1965_ = v_r_1962_;
v_isShared_1966_ = v_isSharedCheck_1987_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v_r_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1987_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
lean_inc(v_a_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 1);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1954_, v_mkInfoTree_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v_a_1961_, v___x_1968_);
lean_dec_ref(v___x_1968_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1977_);
v___x_1971_ = v___x_1969_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v___x_1969_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_a_1963_);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1963_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_a_1963_);
v_a_1978_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1969_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1969_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_a_1988_ = lean_ctor_get(v_r_1962_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v_r_1962_, 1);
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_1954_, v_mkInfoTree_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v_a_1961_, v___x_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1990_, 0);
lean_dec(v_unused_1998_);
v___x_1992_ = v___x_1990_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v___x_1990_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 1);
lean_ctor_set(v___x_1992_, 0, v_a_1988_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1988_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1988_);
v_a_1999_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_2007_, lean_object* v_mkInfoTree_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2007_, v_mkInfoTree_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2017_, lean_object* v_output_2018_, lean_object* v_trees_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_lctx_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_lctx_2027_ = lean_ctor_get(v___y_2022_, 2);
lean_inc_ref(v_lctx_2027_);
v___x_2028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2028_, 0, v_lctx_2027_);
lean_ctor_set(v___x_2028_, 1, v_stx_2017_);
lean_ctor_set(v___x_2028_, 2, v_output_2018_);
v___x_2029_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v_trees_2019_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2032_, lean_object* v_output_2033_, lean_object* v_trees_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2032_, v_output_2033_, v_trees_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2043_, lean_object* v_output_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___f_2053_; lean_object* v___x_2054_; 
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2053_, 0, v_stx_2043_);
lean_closure_set(v___f_2053_, 1, v_output_2044_);
v___x_2054_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2045_, v___f_2053_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2055_, lean_object* v_output_2056_, lean_object* v_x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2055_, v_output_2056_, v_x_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2066_, lean_object* v_afterStx_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_inc_ref(v___y_2069_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2077_, 0, v_x_2068_);
lean_closure_set(v___f_2077_, 1, v___y_2069_);
lean_inc(v_afterStx_2067_);
lean_inc(v_beforeStx_2066_);
v___x_2078_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2078_, 0, lean_box(0));
lean_closure_set(v___x_2078_, 1, v_beforeStx_2066_);
lean_closure_set(v___x_2078_, 2, v_afterStx_2067_);
lean_closure_set(v___x_2078_, 3, v___f_2077_);
v___x_2079_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2066_, v_afterStx_2067_, v___x_2078_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2079_) == 0)
{
return v___x_2079_;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2088_, lean_object* v_afterStx_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2088_, v_afterStx_2089_, v_x_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2099_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2103_ = l_String_toRawSubstring_x27(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2125_, uint8_t v___x_2126_, lean_object* v_config_2127_, lean_object* v_a_2128_, uint8_t v___x_2129_, lean_object* v___x_2130_, lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v___f_2133_, lean_object* v___x_2134_, lean_object* v_body_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_term_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_ref_2152_; lean_object* v___y_2153_; lean_object* v_ref_2159_; lean_object* v_quotContext_2160_; lean_object* v_currMacroScope_2161_; lean_object* v_ref_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_eq_x3f_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_ref_2159_ = lean_ctor_get(v___y_2141_, 5);
v_quotContext_2160_ = lean_ctor_get(v___y_2141_, 10);
v_currMacroScope_2161_ = lean_ctor_get(v___y_2141_, 11);
v_ref_2162_ = l_Lean_replaceRef(v_rhs_2125_, v_ref_2159_);
v___x_2163_ = l_Lean_SourceInfo_fromRef(v_ref_2162_, v___x_2126_);
lean_dec(v_ref_2162_);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2163_, 2);
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2167_ = lean_ctor_get(v_config_2127_, 0);
lean_inc(v_eq_x3f_2167_);
lean_dec_ref(v_config_2127_);
v___x_2168_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2161_);
lean_inc(v_quotContext_2160_);
v___x_2169_ = l_Lean_addMacroScope(v_quotContext_2160_, v___x_2168_, v_currMacroScope_2161_);
v___x_2170_ = lean_box(0);
lean_inc(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2163_);
lean_ctor_set(v___x_2171_, 1, v___x_2166_);
lean_ctor_set(v___x_2171_, 2, v___x_2169_);
lean_ctor_set(v___x_2171_, 3, v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2132_);
lean_inc_ref(v___x_2131_);
lean_inc_ref(v___x_2130_);
v___x_2173_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2172_);
v___x_2174_ = l_Lean_Syntax_node2(v___x_2163_, v___x_2173_, v___x_2165_, v___x_2171_);
if (lean_obj_tag(v_eq_x3f_2167_) == 1)
{
lean_object* v_val_2175_; lean_object* v___x_2176_; 
v_val_2175_ = lean_ctor_get(v_eq_x3f_2167_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v_eq_x3f_2167_, 1);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v_ref_2159_);
v___x_2176_ = lean_apply_9(v___f_2133_, v_ref_2159_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, lean_box(0));
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc_n(v_a_2177_, 23);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2132_, 5);
lean_inc_ref_n(v___x_2131_, 5);
lean_inc_ref_n(v___x_2130_, 5);
v___x_2179_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2181_, 0, v_a_2177_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2177_);
lean_ctor_set(v___x_2182_, 1, v___x_2164_);
v___x_2183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2177_);
lean_ctor_set(v___x_2183_, 1, v___x_2166_);
lean_ctor_set(v___x_2183_, 2, v___x_2169_);
lean_ctor_set(v___x_2183_, 3, v___x_2170_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2177_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_a_2177_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2189_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2188_);
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2177_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2193_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_a_2177_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
v___x_2195_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2196_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2177_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
lean_ctor_set(v___x_2197_, 2, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2199_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2177_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_Syntax_node2(v_a_2177_, v___x_2195_, v_val_2175_, v___x_2201_);
v___x_2203_ = l_Lean_Syntax_node2(v_a_2177_, v___x_2199_, v___x_2202_, v___x_2174_);
v___x_2204_ = l_Lean_Syntax_node1(v_a_2177_, v___x_2195_, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2177_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2208_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2207_);
v___x_2209_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2210_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2177_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_Syntax_node1(v_a_2177_, v___x_2195_, v___x_2134_);
v___x_2214_ = l_Lean_Syntax_node1(v_a_2177_, v___x_2195_, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2177_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_Syntax_node4(v_a_2177_, v___x_2210_, v___x_2212_, v___x_2214_, v___x_2216_, v_body_2135_);
v___x_2218_ = l_Lean_Syntax_node1(v_a_2177_, v___x_2195_, v___x_2217_);
v___x_2219_ = l_Lean_Syntax_node1(v_a_2177_, v___x_2208_, v___x_2218_);
lean_inc_ref(v___x_2197_);
v___x_2220_ = l_Lean_Syntax_node6(v_a_2177_, v___x_2193_, v___x_2194_, v___x_2197_, v___x_2197_, v___x_2204_, v___x_2206_, v___x_2219_);
lean_inc_ref(v___x_2187_);
lean_inc_ref(v___x_2183_);
lean_inc_ref(v___x_2182_);
v___x_2221_ = l_Lean_Syntax_node5(v_a_2177_, v___x_2189_, v___x_2191_, v___x_2182_, v___x_2183_, v___x_2187_, v___x_2220_);
v___x_2222_ = l_Lean_Syntax_node7(v_a_2177_, v___x_2179_, v___x_2181_, v___x_2182_, v___x_2183_, v___x_2185_, v_rhs_2125_, v___x_2187_, v___x_2221_);
lean_inc(v_ref_2159_);
v_term_2145_ = v___x_2222_;
v___y_2146_ = v___y_2136_;
v___y_2147_ = v___y_2137_;
v___y_2148_ = v___y_2138_;
v___y_2149_ = v___y_2139_;
v___y_2150_ = v___y_2140_;
v___y_2151_ = v___y_2141_;
v_ref_2152_ = v_ref_2159_;
v___y_2153_ = v___y_2142_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_val_2175_);
lean_dec(v___x_2174_);
lean_dec(v___x_2169_);
lean_dec(v_body_2135_);
lean_dec(v___x_2134_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_a_2128_);
lean_dec(v_rhs_2125_);
v_a_2223_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2176_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2176_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_eq_x3f_2167_);
lean_inc_ref(v_a_2128_);
v___x_2231_ = l_Lean_Elab_Term_exprToSyntax(v_a_2128_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v_ref_2159_);
v___x_2233_ = lean_apply_9(v___f_2133_, v_ref_2159_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, lean_box(0));
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_n(v_a_2234_, 32);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2132_, 8);
lean_inc_ref_n(v___x_2131_, 8);
lean_inc_ref_n(v___x_2130_, 8);
v___x_2236_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2235_);
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2234_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2234_);
lean_ctor_set(v___x_2239_, 1, v___x_2164_);
v___x_2240_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2234_);
lean_ctor_set(v___x_2240_, 1, v___x_2166_);
lean_ctor_set(v___x_2240_, 2, v___x_2169_);
lean_ctor_set(v___x_2240_, 3, v___x_2170_);
v___x_2241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2234_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_a_2234_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2246_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2245_);
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_a_2234_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2250_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v_a_2234_);
lean_ctor_set(v___x_2251_, 1, v___x_2249_);
v___x_2252_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2253_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2234_);
lean_ctor_set(v___x_2254_, 1, v___x_2252_);
lean_ctor_set(v___x_2254_, 2, v___x_2253_);
v___x_2255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2256_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2255_);
v___x_2257_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_a_2234_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_a_2234_);
lean_ctor_set(v___x_2259_, 1, v___x_2255_);
v___x_2260_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2261_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2260_);
v___x_2262_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2234_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2265_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2264_);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2234_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2265_, v___x_2267_);
v___x_2269_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_a_2234_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_inc_ref_n(v___x_2254_, 2);
v___x_2272_ = l_Lean_Syntax_node5(v_a_2234_, v___x_2261_, v___x_2263_, v___x_2269_, v___x_2254_, v___x_2271_, v_a_2232_);
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2234_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
lean_inc_ref(v___x_2242_);
v___x_2275_ = l_Lean_Syntax_node5(v_a_2234_, v___x_2256_, v___x_2258_, v___x_2259_, v___x_2242_, v___x_2272_, v___x_2274_);
v___x_2276_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2275_);
v___x_2277_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2278_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2277_);
v___x_2279_ = l_Lean_Syntax_node2(v_a_2234_, v___x_2278_, v___x_2254_, v___x_2174_);
v___x_2280_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2234_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2284_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2283_);
v___x_2285_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2286_ = l_Lean_Name_mkStr4(v___x_2130_, v___x_2131_, v___x_2132_, v___x_2285_);
v___x_2287_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_a_2234_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2134_);
v___x_2290_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2289_);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_a_2234_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_Syntax_node4(v_a_2234_, v___x_2286_, v___x_2288_, v___x_2290_, v___x_2292_, v_body_2135_);
v___x_2294_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2252_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node1(v_a_2234_, v___x_2284_, v___x_2294_);
v___x_2296_ = l_Lean_Syntax_node6(v_a_2234_, v___x_2250_, v___x_2251_, v___x_2254_, v___x_2276_, v___x_2280_, v___x_2282_, v___x_2295_);
lean_inc_ref(v___x_2244_);
lean_inc_ref(v___x_2240_);
lean_inc_ref(v___x_2239_);
v___x_2297_ = l_Lean_Syntax_node5(v_a_2234_, v___x_2246_, v___x_2248_, v___x_2239_, v___x_2240_, v___x_2244_, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node7(v_a_2234_, v___x_2236_, v___x_2238_, v___x_2239_, v___x_2240_, v___x_2242_, v_rhs_2125_, v___x_2244_, v___x_2297_);
lean_inc(v_ref_2159_);
v_term_2145_ = v___x_2298_;
v___y_2146_ = v___y_2136_;
v___y_2147_ = v___y_2137_;
v___y_2148_ = v___y_2138_;
v___y_2149_ = v___y_2139_;
v___y_2150_ = v___y_2140_;
v___y_2151_ = v___y_2141_;
v_ref_2152_ = v_ref_2159_;
v___y_2153_ = v___y_2142_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2232_);
lean_dec(v___x_2174_);
lean_dec(v___x_2169_);
lean_dec(v_body_2135_);
lean_dec(v___x_2134_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_a_2128_);
lean_dec(v_rhs_2125_);
v_a_2299_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2233_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2233_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v___x_2174_);
lean_dec(v___x_2169_);
lean_dec(v_body_2135_);
lean_dec(v___x_2134_);
lean_dec_ref(v___f_2133_);
lean_dec_ref(v___x_2132_);
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec_ref(v_a_2128_);
lean_dec(v_rhs_2125_);
v_a_2307_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2231_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2231_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
v___jp_2144_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___f_2157_; lean_object* v___x_2158_; 
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2128_);
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_box(v___x_2129_);
lean_inc(v_term_2145_);
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2157_, 0, v_term_2145_);
lean_closure_set(v___f_2157_, 1, v___x_2154_);
lean_closure_set(v___f_2157_, 2, v___x_2156_);
lean_closure_set(v___f_2157_, 3, v___x_2155_);
v___x_2158_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2152_, v_term_2145_, v___f_2157_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2153_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2315_ = _args[0];
lean_object* v___x_2316_ = _args[1];
lean_object* v_config_2317_ = _args[2];
lean_object* v_a_2318_ = _args[3];
lean_object* v___x_2319_ = _args[4];
lean_object* v___x_2320_ = _args[5];
lean_object* v___x_2321_ = _args[6];
lean_object* v___x_2322_ = _args[7];
lean_object* v___f_2323_ = _args[8];
lean_object* v___x_2324_ = _args[9];
lean_object* v_body_2325_ = _args[10];
lean_object* v___y_2326_ = _args[11];
lean_object* v___y_2327_ = _args[12];
lean_object* v___y_2328_ = _args[13];
lean_object* v___y_2329_ = _args[14];
lean_object* v___y_2330_ = _args[15];
lean_object* v___y_2331_ = _args[16];
lean_object* v___y_2332_ = _args[17];
lean_object* v___y_2333_ = _args[18];
_start:
{
uint8_t v___x_100274__boxed_2334_; uint8_t v___x_100276__boxed_2335_; lean_object* v_res_2336_; 
v___x_100274__boxed_2334_ = lean_unbox(v___x_2316_);
v___x_100276__boxed_2335_ = lean_unbox(v___x_2319_);
v_res_2336_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2315_, v___x_100274__boxed_2334_, v_config_2317_, v_a_2318_, v___x_100276__boxed_2335_, v___x_2320_, v___x_2321_, v___x_2322_, v___f_2323_, v___x_2324_, v_body_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2337_, lean_object* v___y_2338_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v_x_2337_, 0);
lean_inc(v_a_2339_);
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_a_2339_);
lean_ctor_set(v___x_2340_, 1, v___y_2338_);
return v___x_2340_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v_x_2337_, 0);
lean_inc(v_a_2341_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_a_2341_);
lean_ctor_set(v___x_2342_, 1, v___y_2338_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2343_, v___y_2344_);
lean_dec_ref(v_x_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2346_, lean_object* v_stx_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2346_, v_stx_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
if (lean_obj_tag(v_a_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
v_a_2352_ = lean_ctor_get(v___x_2350_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2350_, 0);
lean_dec(v_unused_2361_);
v___x_2354_ = v___x_2350_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_box(0);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_a_2352_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2390_; 
v_val_2362_ = lean_ctor_get(v_a_2351_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2351_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2364_ = v_a_2351_;
v_isShared_2365_ = v_isSharedCheck_2390_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v_a_2351_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2390_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_snd_2366_; 
v_snd_2366_ = lean_ctor_get(v_val_2362_, 1);
lean_inc(v_snd_2366_);
lean_dec(v_val_2362_);
if (lean_obj_tag(v_snd_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2376_; 
lean_del_object(v___x_2364_);
v_a_2367_ = lean_ctor_get(v___x_2350_, 1);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2350_, 2);
v_a_2368_ = lean_ctor_get(v_snd_2366_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_snd_2366_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2370_ = v_snd_2366_;
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v_snd_2366_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2376_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2373_, v_a_2367_);
lean_dec_ref(v___x_2373_);
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2389_; 
v_a_2377_ = lean_ctor_get(v___x_2350_, 1);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2350_, 2);
v_a_2378_ = lean_ctor_get(v_snd_2366_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_snd_2366_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2380_ = v_snd_2366_;
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v_snd_2366_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_a_2378_);
v___x_2383_ = v___x_2364_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2385_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2383_);
v___x_2385_ = v___x_2380_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2385_, v_a_2377_);
lean_dec_ref(v___x_2385_);
return v___x_2386_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2391_ = lean_ctor_get(v___x_2350_, 0);
v_a_2392_ = lean_ctor_get(v___x_2350_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2350_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_inc(v_a_2391_);
lean_dec(v___x_2350_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2391_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2400_, lean_object* v_stx_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2400_, v_stx_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_currNamespace_2405_);
lean_ctor_set(v___x_2408_, 1, v___y_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2409_, v___y_2410_, v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2413_, lean_object* v_currNamespace_2414_, lean_object* v_openDecls_2415_, lean_object* v_n_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = l_Lean_ResolveName_resolveNamespace(v_env_2413_, v_currNamespace_2414_, v_openDecls_2415_, v_n_2416_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2421_, lean_object* v_currNamespace_2422_, lean_object* v_openDecls_2423_, lean_object* v_n_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2421_, v_currNamespace_2422_, v_openDecls_2423_, v_n_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2428_, lean_object* v_declName_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v___x_2432_; lean_object* v_env_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2432_ = 0;
v_env_2433_ = l_Lean_Environment_setExporting(v_env_2428_, v___x_2432_);
lean_inc(v_declName_2429_);
v___x_2434_ = l_Lean_mkPrivateName(v_env_2433_, v_declName_2429_);
v___x_2435_ = 1;
lean_inc_ref(v_env_2433_);
v___x_2436_ = l_Lean_Environment_contains(v_env_2433_, v___x_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2437_ = l_Lean_privateToUserName(v_declName_2429_);
v___x_2438_ = l_Lean_Environment_contains(v_env_2433_, v___x_2437_, v___x_2435_);
v___x_2439_ = lean_box(v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___y_2431_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_env_2433_);
lean_dec(v_declName_2429_);
v___x_2441_ = lean_box(v___x_2436_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___y_2431_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2443_, lean_object* v_declName_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2443_, v_declName_2444_, v___y_2445_, v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2447_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2448_; double v___x_2449_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = lean_float_of_nat(v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2452_, lean_object* v_msg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_ref_2459_; lean_object* v___x_2460_; lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2505_; 
v_ref_2459_ = lean_ctor_get(v___y_2456_, 5);
v___x_2460_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2505_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2505_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v_traceState_2466_; lean_object* v_env_2467_; lean_object* v_nextMacroScope_2468_; lean_object* v_ngen_2469_; lean_object* v_auxDeclNGen_2470_; lean_object* v_cache_2471_; lean_object* v_messages_2472_; lean_object* v_infoState_2473_; lean_object* v_snapshotTasks_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2504_; 
v___x_2465_ = lean_st_ref_take(v___y_2457_);
v_traceState_2466_ = lean_ctor_get(v___x_2465_, 4);
v_env_2467_ = lean_ctor_get(v___x_2465_, 0);
v_nextMacroScope_2468_ = lean_ctor_get(v___x_2465_, 1);
v_ngen_2469_ = lean_ctor_get(v___x_2465_, 2);
v_auxDeclNGen_2470_ = lean_ctor_get(v___x_2465_, 3);
v_cache_2471_ = lean_ctor_get(v___x_2465_, 5);
v_messages_2472_ = lean_ctor_get(v___x_2465_, 6);
v_infoState_2473_ = lean_ctor_get(v___x_2465_, 7);
v_snapshotTasks_2474_ = lean_ctor_get(v___x_2465_, 8);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2476_ = v___x_2465_;
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_snapshotTasks_2474_);
lean_inc(v_infoState_2473_);
lean_inc(v_messages_2472_);
lean_inc(v_cache_2471_);
lean_inc(v_traceState_2466_);
lean_inc(v_auxDeclNGen_2470_);
lean_inc(v_ngen_2469_);
lean_inc(v_nextMacroScope_2468_);
lean_inc(v_env_2467_);
lean_dec(v___x_2465_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
uint64_t v_tid_2478_; lean_object* v_traces_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2503_; 
v_tid_2478_ = lean_ctor_get_uint64(v_traceState_2466_, sizeof(void*)*1);
v_traces_2479_ = lean_ctor_get(v_traceState_2466_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_traceState_2466_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2481_ = v_traceState_2466_;
v_isShared_2482_ = v_isSharedCheck_2503_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_traces_2479_);
lean_dec(v_traceState_2466_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2503_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; double v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2485_ = 0;
v___x_2486_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2487_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2487_, 0, v_cls_2452_);
lean_ctor_set(v___x_2487_, 1, v___x_2483_);
lean_ctor_set(v___x_2487_, 2, v___x_2486_);
lean_ctor_set_float(v___x_2487_, sizeof(void*)*3, v___x_2484_);
lean_ctor_set_float(v___x_2487_, sizeof(void*)*3 + 8, v___x_2484_);
lean_ctor_set_uint8(v___x_2487_, sizeof(void*)*3 + 16, v___x_2485_);
v___x_2488_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2489_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v_a_2461_);
lean_ctor_set(v___x_2489_, 2, v___x_2488_);
lean_inc(v_ref_2459_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_ref_2459_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_PersistentArray_push___redArg(v_traces_2479_, v___x_2490_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2491_);
v___x_2493_ = v___x_2481_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2491_);
lean_ctor_set_uint64(v_reuseFailAlloc_2502_, sizeof(void*)*1, v_tid_2478_);
v___x_2493_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v___x_2493_);
v___x_2495_ = v___x_2476_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_env_2467_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_nextMacroScope_2468_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_ngen_2469_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_auxDeclNGen_2470_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2501_, 5, v_cache_2471_);
lean_ctor_set(v_reuseFailAlloc_2501_, 6, v_messages_2472_);
lean_ctor_set(v_reuseFailAlloc_2501_, 7, v_infoState_2473_);
lean_ctor_set(v_reuseFailAlloc_2501_, 8, v_snapshotTasks_2474_);
v___x_2495_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2496_ = lean_st_ref_set(v___y_2457_, v___x_2495_);
v___x_2497_ = lean_box(0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2497_);
v___x_2499_ = v___x_2463_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2506_, lean_object* v_msg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2506_, v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
if (lean_obj_tag(v_as_2517_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
else
{
lean_object* v_options_2528_; uint8_t v_hasTrace_2529_; 
v_options_2528_ = lean_ctor_get(v___y_2523_, 2);
v_hasTrace_2529_ = lean_ctor_get_uint8(v_options_2528_, sizeof(void*)*1);
if (v_hasTrace_2529_ == 0)
{
lean_object* v_tail_2530_; 
v_tail_2530_ = lean_ctor_get(v_as_2517_, 1);
lean_inc(v_tail_2530_);
lean_dec_ref_known(v_as_2517_, 2);
v_as_2517_ = v_tail_2530_;
goto _start;
}
else
{
lean_object* v_head_2532_; lean_object* v_tail_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v_inheritedTraceOptions_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_head_2532_ = lean_ctor_get(v_as_2517_, 0);
lean_inc(v_head_2532_);
v_tail_2533_ = lean_ctor_get(v_as_2517_, 1);
lean_inc(v_tail_2533_);
lean_dec_ref_known(v_as_2517_, 2);
v_fst_2534_ = lean_ctor_get(v_head_2532_, 0);
lean_inc_n(v_fst_2534_, 2);
v_snd_2535_ = lean_ctor_get(v_head_2532_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_head_2532_);
v_inheritedTraceOptions_2536_ = lean_ctor_get(v___y_2523_, 13);
v___x_2537_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2538_ = l_Lean_Name_append(v___x_2537_, v_fst_2534_);
v___x_2539_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2536_, v_options_2528_, v___x_2538_);
lean_dec(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_dec(v_snd_2535_);
lean_dec(v_fst_2534_);
v_as_2517_ = v_tail_2533_;
goto _start;
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_snd_2535_);
v___x_2542_ = l_Lean_MessageData_ofFormat(v___x_2541_);
v___x_2543_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2534_, v___x_2542_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_dec_ref_known(v___x_2543_, 1);
v_as_2517_ = v_tail_2533_;
goto _start;
}
else
{
lean_dec(v_tail_2533_);
return v___x_2543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2554_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2555_, lean_object* v_i_2556_, lean_object* v_k_2557_){
_start:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_array_get_size(v_keys_2555_);
v___x_2559_ = lean_nat_dec_lt(v_i_2556_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec(v_i_2556_);
return v___x_2559_;
}
else
{
lean_object* v_k_x27_2560_; uint8_t v___x_2561_; 
v_k_x27_2560_ = lean_array_fget_borrowed(v_keys_2555_, v_i_2556_);
v___x_2561_ = l_Lean_instBEqExtraModUse_beq(v_k_2557_, v_k_x27_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = lean_nat_add(v_i_2556_, v___x_2562_);
lean_dec(v_i_2556_);
v_i_2556_ = v___x_2563_;
goto _start;
}
else
{
lean_dec(v_i_2556_);
return v___x_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2565_, lean_object* v_i_2566_, lean_object* v_k_2567_){
_start:
{
uint8_t v_res_2568_; lean_object* v_r_2569_; 
v_res_2568_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2565_, v_i_2566_, v_k_2567_);
lean_dec_ref(v_k_2567_);
lean_dec_ref(v_keys_2565_);
v_r_2569_ = lean_box(v_res_2568_);
return v_r_2569_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2570_, size_t v_x_2571_, lean_object* v_x_2572_){
_start:
{
if (lean_obj_tag(v_x_2570_) == 0)
{
lean_object* v_es_2573_; lean_object* v___x_2574_; size_t v___x_2575_; size_t v___x_2576_; lean_object* v_j_2577_; lean_object* v___x_2578_; 
v_es_2573_ = lean_ctor_get(v_x_2570_, 0);
v___x_2574_ = lean_box(2);
v___x_2575_ = ((size_t)31ULL);
v___x_2576_ = lean_usize_land(v_x_2571_, v___x_2575_);
v_j_2577_ = lean_usize_to_nat(v___x_2576_);
v___x_2578_ = lean_array_get_borrowed(v___x_2574_, v_es_2573_, v_j_2577_);
lean_dec(v_j_2577_);
switch(lean_obj_tag(v___x_2578_))
{
case 0:
{
lean_object* v_key_2579_; uint8_t v___x_2580_; 
v_key_2579_ = lean_ctor_get(v___x_2578_, 0);
v___x_2580_ = l_Lean_instBEqExtraModUse_beq(v_x_2572_, v_key_2579_);
return v___x_2580_;
}
case 1:
{
lean_object* v_node_2581_; size_t v___x_2582_; size_t v___x_2583_; 
v_node_2581_ = lean_ctor_get(v___x_2578_, 0);
v___x_2582_ = ((size_t)5ULL);
v___x_2583_ = lean_usize_shift_right(v_x_2571_, v___x_2582_);
v_x_2570_ = v_node_2581_;
v_x_2571_ = v___x_2583_;
goto _start;
}
default: 
{
uint8_t v___x_2585_; 
v___x_2585_ = 0;
return v___x_2585_;
}
}
}
else
{
lean_object* v_ks_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v_ks_2586_ = lean_ctor_get(v_x_2570_, 0);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2586_, v___x_2587_, v_x_2572_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
size_t v_x_101018__boxed_2592_; uint8_t v_res_2593_; lean_object* v_r_2594_; 
v_x_101018__boxed_2592_ = lean_unbox_usize(v_x_2590_);
lean_dec(v_x_2590_);
v_res_2593_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2589_, v_x_101018__boxed_2592_, v_x_2591_);
lean_dec_ref(v_x_2591_);
lean_dec_ref(v_x_2589_);
v_r_2594_ = lean_box(v_res_2593_);
return v_r_2594_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
uint64_t v___x_2597_; size_t v___x_2598_; uint8_t v___x_2599_; 
v___x_2597_ = l_Lean_instHashableExtraModUse_hash(v_x_2596_);
v___x_2598_ = lean_uint64_to_usize(v___x_2597_);
v___x_2599_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2595_, v___x_2598_, v_x_2596_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2600_, lean_object* v_x_2601_){
_start:
{
uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_res_2602_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2600_, v_x_2601_);
lean_dec_ref(v_x_2601_);
lean_dec_ref(v_x_2600_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2607_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2608_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2609_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2615_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
lean_ctor_set(v___x_2615_, 2, v___x_2614_);
lean_ctor_set(v___x_2615_, 3, v___x_2614_);
lean_ctor_set(v___x_2615_, 4, v___x_2614_);
lean_ctor_set(v___x_2615_, 5, v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2626_ = l_Lean_stringToMessageData(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_cls_2627_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2628_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2629_ = l_Lean_Name_append(v___x_2628_, v_cls_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2640_, uint8_t v_isMeta_2641_, lean_object* v_hint_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v_env_2652_; uint8_t v_isExporting_2653_; lean_object* v___x_2654_; lean_object* v_env_2655_; lean_object* v___x_2656_; lean_object* v_entry_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___x_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; 
v___x_2651_ = lean_st_ref_get(v___y_2649_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v_isExporting_2653_ = lean_ctor_get_uint8(v_env_2652_, sizeof(void*)*8);
lean_dec_ref(v_env_2652_);
v___x_2654_ = lean_st_ref_get(v___y_2649_);
v_env_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc_ref(v_env_2655_);
lean_dec(v___x_2654_);
v___x_2656_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2640_);
v_entry_2657_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2657_, 0, v_mod_2640_);
lean_ctor_set_uint8(v_entry_2657_, sizeof(void*)*1, v_isExporting_2653_);
lean_ctor_set_uint8(v_entry_2657_, sizeof(void*)*1 + 1, v_isMeta_2641_);
v___x_2658_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2659_ = lean_box(1);
v___x_2660_ = lean_box(0);
v___x_2703_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2656_, v___x_2658_, v_env_2655_, v___x_2659_, v___x_2660_);
v___x_2704_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2703_, v_entry_2657_);
lean_dec(v___x_2703_);
v___x_2705_ = lean_bool_not(v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref_known(v_entry_2657_, 1);
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
else
{
lean_object* v_options_2708_; uint8_t v_hasTrace_2709_; 
v_options_2708_ = lean_ctor_get(v___y_2648_, 2);
v_hasTrace_2709_ = lean_ctor_get_uint8(v_options_2708_, sizeof(void*)*1);
if (v_hasTrace_2709_ == 0)
{
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___y_2662_ = v___y_2647_;
v___y_2663_ = v___y_2649_;
goto v___jp_2661_;
}
else
{
lean_object* v_inheritedTraceOptions_2710_; lean_object* v_cls_2711_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_inheritedTraceOptions_2710_ = lean_ctor_get(v___y_2648_, 13);
v_cls_2711_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2731_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2710_, v_options_2708_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_dec(v_hint_2642_);
lean_dec(v_mod_2640_);
v___y_2662_ = v___y_2647_;
v___y_2663_ = v___y_2649_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2733_; lean_object* v___y_2735_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2653_ == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2735_ = v___x_2742_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2743_; 
v___x_2743_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2735_ = v___x_2743_;
goto v___jp_2734_;
}
v___jp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_inc_ref(v___y_2735_);
v___x_2736_ = l_Lean_stringToMessageData(v___y_2735_);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2733_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
if (v_isMeta_2641_ == 0)
{
lean_object* v___x_2740_; 
v___x_2740_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2718_ = v___x_2739_;
v___y_2719_ = v___x_2740_;
goto v___jp_2717_;
}
else
{
lean_object* v___x_2741_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2718_ = v___x_2739_;
v___y_2719_ = v___x_2741_;
goto v___jp_2717_;
}
}
}
v___jp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2713_);
lean_ctor_set(v___x_2715_, 1, v___y_2714_);
v___x_2716_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2711_, v___x_2715_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref_known(v___x_2716_, 1);
v___y_2662_ = v___y_2647_;
v___y_2663_ = v___y_2649_;
goto v___jp_2661_;
}
else
{
lean_dec_ref_known(v_entry_2657_, 1);
return v___x_2716_;
}
}
v___jp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
lean_inc_ref(v___y_2719_);
v___x_2720_ = l_Lean_stringToMessageData(v___y_2719_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___y_2718_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = l_Lean_MessageData_ofName(v_mod_2640_);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_Name_isAnonymous(v_hint_2642_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2728_ = l_Lean_MessageData_ofName(v_hint_2642_);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___y_2713_ = v___x_2725_;
v___y_2714_ = v___x_2729_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_hint_2642_);
v___x_2730_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2713_ = v___x_2725_;
v___y_2714_ = v___x_2730_;
goto v___jp_2712_;
}
}
}
}
v___jp_2661_:
{
lean_object* v___x_2664_; lean_object* v_toEnvExtension_2665_; lean_object* v_env_2666_; lean_object* v_nextMacroScope_2667_; lean_object* v_ngen_2668_; lean_object* v_auxDeclNGen_2669_; lean_object* v_traceState_2670_; lean_object* v_messages_2671_; lean_object* v_infoState_2672_; lean_object* v_snapshotTasks_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2701_; 
v___x_2664_ = lean_st_ref_take(v___y_2663_);
v_toEnvExtension_2665_ = lean_ctor_get(v___x_2658_, 0);
v_env_2666_ = lean_ctor_get(v___x_2664_, 0);
v_nextMacroScope_2667_ = lean_ctor_get(v___x_2664_, 1);
v_ngen_2668_ = lean_ctor_get(v___x_2664_, 2);
v_auxDeclNGen_2669_ = lean_ctor_get(v___x_2664_, 3);
v_traceState_2670_ = lean_ctor_get(v___x_2664_, 4);
v_messages_2671_ = lean_ctor_get(v___x_2664_, 6);
v_infoState_2672_ = lean_ctor_get(v___x_2664_, 7);
v_snapshotTasks_2673_ = lean_ctor_get(v___x_2664_, 8);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2664_, 5);
lean_dec(v_unused_2702_);
v___x_2675_ = v___x_2664_;
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_snapshotTasks_2673_);
lean_inc(v_infoState_2672_);
lean_inc(v_messages_2671_);
lean_inc(v_traceState_2670_);
lean_inc(v_auxDeclNGen_2669_);
lean_inc(v_ngen_2668_);
lean_inc(v_nextMacroScope_2667_);
lean_inc(v_env_2666_);
lean_dec(v___x_2664_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_asyncMode_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v_asyncMode_2677_ = lean_ctor_get(v_toEnvExtension_2665_, 2);
v___x_2678_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2658_, v_env_2666_, v_entry_2657_, v_asyncMode_2677_, v___x_2660_);
v___x_2679_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 5, v___x_2679_);
lean_ctor_set(v___x_2675_, 0, v___x_2678_);
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_nextMacroScope_2667_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_ngen_2668_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_auxDeclNGen_2669_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_traceState_2670_);
lean_ctor_set(v_reuseFailAlloc_2700_, 5, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2700_, 6, v_messages_2671_);
lean_ctor_set(v_reuseFailAlloc_2700_, 7, v_infoState_2672_);
lean_ctor_set(v_reuseFailAlloc_2700_, 8, v_snapshotTasks_2673_);
v___x_2681_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_mctx_2684_; lean_object* v_zetaDeltaFVarIds_2685_; lean_object* v_postponed_2686_; lean_object* v_diag_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2698_; 
v___x_2682_ = lean_st_ref_set(v___y_2663_, v___x_2681_);
v___x_2683_ = lean_st_ref_take(v___y_2662_);
v_mctx_2684_ = lean_ctor_get(v___x_2683_, 0);
v_zetaDeltaFVarIds_2685_ = lean_ctor_get(v___x_2683_, 2);
v_postponed_2686_ = lean_ctor_get(v___x_2683_, 3);
v_diag_2687_ = lean_ctor_get(v___x_2683_, 4);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2683_, 1);
lean_dec(v_unused_2699_);
v___x_2689_ = v___x_2683_;
v_isShared_2690_ = v_isSharedCheck_2698_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_diag_2687_);
lean_inc(v_postponed_2686_);
lean_inc(v_zetaDeltaFVarIds_2685_);
lean_inc(v_mctx_2684_);
lean_dec(v___x_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2698_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_mctx_2684_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_zetaDeltaFVarIds_2685_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_postponed_2686_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_diag_2687_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_st_ref_set(v___y_2662_, v___x_2693_);
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2744_, lean_object* v_isMeta_2745_, lean_object* v_hint_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
uint8_t v_isMeta_boxed_2755_; lean_object* v_res_2756_; 
v_isMeta_boxed_2755_ = lean_unbox(v_isMeta_2745_);
v_res_2756_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2744_, v_isMeta_boxed_2755_, v_hint_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2757_, lean_object* v_declName_2758_, lean_object* v_as_2759_, size_t v_sz_2760_, size_t v_i_2761_, lean_object* v_b_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v___x_2771_; 
v___x_2771_ = lean_usize_dec_lt(v_i_2761_, v_sz_2760_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
lean_dec(v_declName_2758_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_b_2762_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; lean_object* v_modules_2774_; lean_object* v___x_2775_; lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v_toImport_2778_; lean_object* v_module_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; 
v___x_2773_ = l_Lean_Environment_header(v___x_2757_);
v_modules_2774_ = lean_ctor_get(v___x_2773_, 3);
lean_inc_ref(v_modules_2774_);
lean_dec_ref(v___x_2773_);
v___x_2775_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2776_ = lean_array_uget_borrowed(v_as_2759_, v_i_2761_);
v___x_2777_ = lean_array_get(v___x_2775_, v_modules_2774_, v_a_2776_);
lean_dec_ref(v_modules_2774_);
v_toImport_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_toImport_2778_);
lean_dec(v___x_2777_);
v_module_2779_ = lean_ctor_get(v_toImport_2778_, 0);
lean_inc(v_module_2779_);
lean_dec_ref(v_toImport_2778_);
v___x_2780_ = 0;
lean_inc(v_declName_2758_);
v___x_2781_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2779_, v___x_2780_, v_declName_2758_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v___x_2782_; size_t v___x_2783_; size_t v___x_2784_; 
lean_dec_ref_known(v___x_2781_, 1);
v___x_2782_ = lean_box(0);
v___x_2783_ = ((size_t)1ULL);
v___x_2784_ = lean_usize_add(v_i_2761_, v___x_2783_);
v_i_2761_ = v___x_2784_;
v_b_2762_ = v___x_2782_;
goto _start;
}
else
{
lean_dec(v_declName_2758_);
return v___x_2781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2786_, lean_object* v_declName_2787_, lean_object* v_as_2788_, lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2786_, v_declName_2787_, v_as_2788_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_as_2788_);
lean_dec_ref(v___x_2786_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_a_2803_, lean_object* v_x_2804_){
_start:
{
if (lean_obj_tag(v_x_2804_) == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_box(0);
return v___x_2805_;
}
else
{
lean_object* v_key_2806_; lean_object* v_value_2807_; lean_object* v_tail_2808_; uint8_t v___x_2809_; 
v_key_2806_ = lean_ctor_get(v_x_2804_, 0);
v_value_2807_ = lean_ctor_get(v_x_2804_, 1);
v_tail_2808_ = lean_ctor_get(v_x_2804_, 2);
v___x_2809_ = lean_name_eq(v_key_2806_, v_a_2803_);
if (v___x_2809_ == 0)
{
v_x_2804_ = v_tail_2808_;
goto _start;
}
else
{
lean_object* v___x_2811_; 
lean_inc(v_value_2807_);
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_value_2807_);
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_2812_, lean_object* v_x_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2812_, v_x_2813_);
lean_dec(v_x_2813_);
lean_dec(v_a_2812_);
return v_res_2814_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2815_; uint64_t v___x_2816_; 
v___x_2815_ = lean_unsigned_to_nat(1723u);
v___x_2816_ = lean_uint64_of_nat(v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_buckets_2819_; lean_object* v___x_2820_; uint64_t v___y_2822_; 
v_buckets_2819_ = lean_ctor_get(v_m_2817_, 1);
v___x_2820_ = lean_array_get_size(v_buckets_2819_);
if (lean_obj_tag(v_a_2818_) == 0)
{
uint64_t v___x_2836_; 
v___x_2836_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0);
v___y_2822_ = v___x_2836_;
goto v___jp_2821_;
}
else
{
uint64_t v_hash_2837_; 
v_hash_2837_ = lean_ctor_get_uint64(v_a_2818_, sizeof(void*)*2);
v___y_2822_ = v_hash_2837_;
goto v___jp_2821_;
}
v___jp_2821_:
{
uint64_t v___x_2823_; uint64_t v___x_2824_; uint64_t v_fold_2825_; uint64_t v___x_2826_; uint64_t v___x_2827_; uint64_t v___x_2828_; size_t v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; size_t v___x_2832_; size_t v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2823_ = 32ULL;
v___x_2824_ = lean_uint64_shift_right(v___y_2822_, v___x_2823_);
v_fold_2825_ = lean_uint64_xor(v___y_2822_, v___x_2824_);
v___x_2826_ = 16ULL;
v___x_2827_ = lean_uint64_shift_right(v_fold_2825_, v___x_2826_);
v___x_2828_ = lean_uint64_xor(v_fold_2825_, v___x_2827_);
v___x_2829_ = lean_uint64_to_usize(v___x_2828_);
v___x_2830_ = lean_usize_of_nat(v___x_2820_);
v___x_2831_ = ((size_t)1ULL);
v___x_2832_ = lean_usize_sub(v___x_2830_, v___x_2831_);
v___x_2833_ = lean_usize_land(v___x_2829_, v___x_2832_);
v___x_2834_ = lean_array_uget_borrowed(v_buckets_2819_, v___x_2833_);
v___x_2835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2818_, v___x_2834_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_m_2838_);
return v_res_2840_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2844_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2845_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2844_, v___x_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2848_, uint8_t v_isMeta_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v_env_2862_; lean_object* v___y_2864_; lean_object* v___x_2877_; 
v___x_2858_ = lean_st_ref_get(v___y_2856_);
v_env_2862_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_env_2862_);
lean_dec(v___x_2858_);
v___x_2877_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2862_, v_declName_2848_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_dec_ref(v_env_2862_);
lean_dec(v_declName_2848_);
goto v___jp_2859_;
}
else
{
lean_object* v_val_2878_; lean_object* v___x_2879_; lean_object* v_modules_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v_val_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = l_Lean_Environment_header(v_env_2862_);
v_modules_2880_ = lean_ctor_get(v___x_2879_, 3);
lean_inc_ref(v_modules_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_array_get_size(v_modules_2880_);
v___x_2882_ = lean_nat_dec_lt(v_val_2878_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_dec_ref(v_modules_2880_);
lean_dec(v_val_2878_);
lean_dec_ref(v_env_2862_);
lean_dec(v_declName_2848_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2883_; lean_object* v_env_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___y_2888_; 
v___x_2883_ = lean_st_ref_get(v___y_2856_);
v_env_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_ref(v_env_2884_);
lean_dec(v___x_2883_);
v___x_2885_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_2886_ = lean_array_fget(v_modules_2880_, v_val_2878_);
lean_dec(v_val_2878_);
lean_dec_ref(v_modules_2880_);
if (v_isMeta_2849_ == 0)
{
lean_dec_ref(v_env_2884_);
v___y_2888_ = v_isMeta_2849_;
goto v___jp_2887_;
}
else
{
uint8_t v___x_2899_; uint8_t v___x_2900_; 
lean_inc(v_declName_2848_);
v___x_2899_ = l_Lean_isMarkedMeta(v_env_2884_, v_declName_2848_);
v___x_2900_ = lean_bool_not(v___x_2899_);
v___y_2888_ = v___x_2900_;
goto v___jp_2887_;
}
v___jp_2887_:
{
lean_object* v_toImport_2889_; lean_object* v_module_2890_; lean_object* v___x_2891_; 
v_toImport_2889_ = lean_ctor_get(v___x_2886_, 0);
lean_inc_ref(v_toImport_2889_);
lean_dec(v___x_2886_);
v_module_2890_ = lean_ctor_get(v_toImport_2889_, 0);
lean_inc(v_module_2890_);
lean_dec_ref(v_toImport_2889_);
lean_inc(v_declName_2848_);
v___x_2891_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2890_, v___y_2888_, v_declName_2848_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec_ref_known(v___x_2891_, 1);
v___x_2892_ = l_Lean_indirectModUseExt;
v___x_2893_ = lean_box(1);
v___x_2894_ = lean_box(0);
lean_inc_ref(v_env_2862_);
v___x_2895_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2885_, v___x_2892_, v_env_2862_, v___x_2893_, v___x_2894_);
v___x_2896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_2895_, v_declName_2848_);
lean_dec(v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2864_ = v___x_2897_;
goto v___jp_2863_;
}
else
{
lean_object* v_val_2898_; 
v_val_2898_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v___x_2896_, 1);
v___y_2864_ = v_val_2898_;
goto v___jp_2863_;
}
}
else
{
lean_dec_ref(v_env_2862_);
lean_dec(v_declName_2848_);
return v___x_2891_;
}
}
}
}
v___jp_2859_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; size_t v_sz_2866_; size_t v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_box(0);
v_sz_2866_ = lean_array_size(v___y_2864_);
v___x_2867_ = ((size_t)0ULL);
v___x_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2862_, v_declName_2848_, v___y_2864_, v_sz_2866_, v___x_2867_, v___x_2865_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_env_2862_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___x_2868_, 0);
lean_dec(v_unused_2876_);
v___x_2870_ = v___x_2868_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_dec(v___x_2868_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2865_);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2865_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
else
{
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_2901_, lean_object* v_isMeta_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_isMeta_boxed_2911_; lean_object* v_res_2912_; 
v_isMeta_boxed_2911_ = lean_unbox(v_isMeta_2902_);
v_res_2912_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_2901_, v_isMeta_boxed_2911_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
if (lean_obj_tag(v_as_x27_2913_) == 0)
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_b_2914_);
return v___x_2923_;
}
else
{
lean_object* v_head_2924_; lean_object* v_tail_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; 
v_head_2924_ = lean_ctor_get(v_as_x27_2913_, 0);
v_tail_2925_ = lean_ctor_get(v_as_x27_2913_, 1);
v___x_2926_ = 1;
lean_inc(v_head_2924_);
v___x_2927_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_2924_, v___x_2926_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2928_; 
lean_dec_ref_known(v___x_2927_, 1);
v___x_2928_ = lean_box(0);
v_as_x27_2913_ = v_tail_2925_;
v_b_2914_ = v___x_2928_;
goto _start;
}
else
{
return v___x_2927_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_2930_, lean_object* v_b_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_2930_, v_b_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_as_x27_2930_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_2941_, lean_object* v_options_2942_, lean_object* v_currNamespace_2943_, lean_object* v_openDecls_2944_, lean_object* v_n_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = l_Lean_ResolveName_resolveGlobalName(v_env_2941_, v_options_2942_, v_currNamespace_2943_, v_openDecls_2944_, v_n_2945_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___y_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_2950_, lean_object* v_options_2951_, lean_object* v_currNamespace_2952_, lean_object* v_openDecls_2953_, lean_object* v_n_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_2950_, v_options_2951_, v_currNamespace_2952_, v_openDecls_2953_, v_n_2954_, v___y_2955_, v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v_options_2951_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_2958_, lean_object* v_msg_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_fileName_2965_; lean_object* v_fileMap_2966_; lean_object* v_options_2967_; lean_object* v_currRecDepth_2968_; lean_object* v_maxRecDepth_2969_; lean_object* v_ref_2970_; lean_object* v_currNamespace_2971_; lean_object* v_openDecls_2972_; lean_object* v_initHeartbeats_2973_; lean_object* v_maxHeartbeats_2974_; lean_object* v_quotContext_2975_; lean_object* v_currMacroScope_2976_; uint8_t v_diag_2977_; lean_object* v_cancelTk_x3f_2978_; uint8_t v_suppressElabErrors_2979_; lean_object* v_inheritedTraceOptions_2980_; lean_object* v_ref_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_fileName_2965_ = lean_ctor_get(v___y_2962_, 0);
v_fileMap_2966_ = lean_ctor_get(v___y_2962_, 1);
v_options_2967_ = lean_ctor_get(v___y_2962_, 2);
v_currRecDepth_2968_ = lean_ctor_get(v___y_2962_, 3);
v_maxRecDepth_2969_ = lean_ctor_get(v___y_2962_, 4);
v_ref_2970_ = lean_ctor_get(v___y_2962_, 5);
v_currNamespace_2971_ = lean_ctor_get(v___y_2962_, 6);
v_openDecls_2972_ = lean_ctor_get(v___y_2962_, 7);
v_initHeartbeats_2973_ = lean_ctor_get(v___y_2962_, 8);
v_maxHeartbeats_2974_ = lean_ctor_get(v___y_2962_, 9);
v_quotContext_2975_ = lean_ctor_get(v___y_2962_, 10);
v_currMacroScope_2976_ = lean_ctor_get(v___y_2962_, 11);
v_diag_2977_ = lean_ctor_get_uint8(v___y_2962_, sizeof(void*)*14);
v_cancelTk_x3f_2978_ = lean_ctor_get(v___y_2962_, 12);
v_suppressElabErrors_2979_ = lean_ctor_get_uint8(v___y_2962_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2980_ = lean_ctor_get(v___y_2962_, 13);
v_ref_2981_ = l_Lean_replaceRef(v_ref_2958_, v_ref_2970_);
lean_inc_ref(v_inheritedTraceOptions_2980_);
lean_inc(v_cancelTk_x3f_2978_);
lean_inc(v_currMacroScope_2976_);
lean_inc(v_quotContext_2975_);
lean_inc(v_maxHeartbeats_2974_);
lean_inc(v_initHeartbeats_2973_);
lean_inc(v_openDecls_2972_);
lean_inc(v_currNamespace_2971_);
lean_inc(v_maxRecDepth_2969_);
lean_inc(v_currRecDepth_2968_);
lean_inc_ref(v_options_2967_);
lean_inc_ref(v_fileMap_2966_);
lean_inc_ref(v_fileName_2965_);
v___x_2982_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2982_, 0, v_fileName_2965_);
lean_ctor_set(v___x_2982_, 1, v_fileMap_2966_);
lean_ctor_set(v___x_2982_, 2, v_options_2967_);
lean_ctor_set(v___x_2982_, 3, v_currRecDepth_2968_);
lean_ctor_set(v___x_2982_, 4, v_maxRecDepth_2969_);
lean_ctor_set(v___x_2982_, 5, v_ref_2981_);
lean_ctor_set(v___x_2982_, 6, v_currNamespace_2971_);
lean_ctor_set(v___x_2982_, 7, v_openDecls_2972_);
lean_ctor_set(v___x_2982_, 8, v_initHeartbeats_2973_);
lean_ctor_set(v___x_2982_, 9, v_maxHeartbeats_2974_);
lean_ctor_set(v___x_2982_, 10, v_quotContext_2975_);
lean_ctor_set(v___x_2982_, 11, v_currMacroScope_2976_);
lean_ctor_set(v___x_2982_, 12, v_cancelTk_x3f_2978_);
lean_ctor_set(v___x_2982_, 13, v_inheritedTraceOptions_2980_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*14, v_diag_2977_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*14 + 1, v_suppressElabErrors_2979_);
v___x_2983_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_2959_, v___y_2960_, v___y_2961_, v___x_2982_, v___y_2963_);
lean_dec_ref_known(v___x_2982_, 14);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_2984_, lean_object* v_msg_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_2984_, v_msg_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v_ref_2984_);
return v_res_2991_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = l_Lean_maxRecDepthErrorMessage;
v___x_2998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_3000_ = l_Lean_MessageData_ofFormat(v___x_2999_);
return v___x_3000_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3002_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3003_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v___x_3001_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_ref_3004_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v_env_3023_; lean_object* v_options_3024_; lean_object* v_currRecDepth_3025_; lean_object* v_maxRecDepth_3026_; lean_object* v_ref_3027_; lean_object* v_currNamespace_3028_; lean_object* v_openDecls_3029_; lean_object* v_quotContext_3030_; lean_object* v_currMacroScope_3031_; lean_object* v___x_3032_; lean_object* v_nextMacroScope_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___f_3038_; lean_object* v_methods_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3022_ = lean_st_ref_get(v___y_3020_);
v_env_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref_n(v_env_3023_, 4);
lean_dec(v___x_3022_);
v_options_3024_ = lean_ctor_get(v___y_3019_, 2);
v_currRecDepth_3025_ = lean_ctor_get(v___y_3019_, 3);
v_maxRecDepth_3026_ = lean_ctor_get(v___y_3019_, 4);
v_ref_3027_ = lean_ctor_get(v___y_3019_, 5);
v_currNamespace_3028_ = lean_ctor_get(v___y_3019_, 6);
v_openDecls_3029_ = lean_ctor_get(v___y_3019_, 7);
v_quotContext_3030_ = lean_ctor_get(v___y_3019_, 10);
v_currMacroScope_3031_ = lean_ctor_get(v___y_3019_, 11);
v___x_3032_ = lean_st_ref_get(v___y_3020_);
v_nextMacroScope_3033_ = lean_ctor_get(v___x_3032_, 1);
lean_inc(v_nextMacroScope_3033_);
lean_dec(v___x_3032_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3034_, 0, v_env_3023_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3035_, 0, v_env_3023_);
lean_inc_n(v_openDecls_3029_, 2);
lean_inc_n(v_currNamespace_3028_, 3);
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3036_, 0, v_env_3023_);
lean_closure_set(v___f_3036_, 1, v_currNamespace_3028_);
lean_closure_set(v___f_3036_, 2, v_openDecls_3029_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3037_, 0, v_currNamespace_3028_);
lean_inc_ref(v_options_3024_);
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3038_, 0, v_env_3023_);
lean_closure_set(v___f_3038_, 1, v_options_3024_);
lean_closure_set(v___f_3038_, 2, v_currNamespace_3028_);
lean_closure_set(v___f_3038_, 3, v_openDecls_3029_);
v_methods_3039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3039_, 0, v___f_3034_);
lean_ctor_set(v_methods_3039_, 1, v___f_3037_);
lean_ctor_set(v_methods_3039_, 2, v___f_3035_);
lean_ctor_set(v_methods_3039_, 3, v___f_3036_);
lean_ctor_set(v_methods_3039_, 4, v___f_3038_);
lean_inc(v_ref_3027_);
lean_inc(v_maxRecDepth_3026_);
lean_inc(v_currRecDepth_3025_);
lean_inc(v_currMacroScope_3031_);
lean_inc(v_quotContext_3030_);
v___x_3040_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3040_, 0, v_methods_3039_);
lean_ctor_set(v___x_3040_, 1, v_quotContext_3030_);
lean_ctor_set(v___x_3040_, 2, v_currMacroScope_3031_);
lean_ctor_set(v___x_3040_, 3, v_currRecDepth_3025_);
lean_ctor_set(v___x_3040_, 4, v_maxRecDepth_3026_);
lean_ctor_set(v___x_3040_, 5, v_ref_3027_);
v___x_3041_ = lean_box(0);
v___x_3042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3042_, 0, v_nextMacroScope_3033_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
v___x_3043_ = lean_apply_2(v_x_3013_, v___x_3040_, v___x_3042_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_a_3045_; lean_object* v_macroScope_3046_; lean_object* v_traceMsgs_3047_; lean_object* v_expandedMacroDecls_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 1);
lean_inc(v_a_3044_);
v_a_3045_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3043_, 2);
v_macroScope_3046_ = lean_ctor_get(v_a_3044_, 0);
lean_inc(v_macroScope_3046_);
v_traceMsgs_3047_ = lean_ctor_get(v_a_3044_, 1);
lean_inc(v_traceMsgs_3047_);
v_expandedMacroDecls_3048_ = lean_ctor_get(v_a_3044_, 2);
lean_inc(v_expandedMacroDecls_3048_);
lean_dec(v_a_3044_);
v___x_3049_ = lean_box(0);
v___x_3050_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3048_, v___x_3049_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v_expandedMacroDecls_3048_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3051_; lean_object* v_env_3052_; lean_object* v_ngen_3053_; lean_object* v_auxDeclNGen_3054_; lean_object* v_traceState_3055_; lean_object* v_cache_3056_; lean_object* v_messages_3057_; lean_object* v_infoState_3058_; lean_object* v_snapshotTasks_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref_known(v___x_3050_, 1);
v___x_3051_ = lean_st_ref_take(v___y_3020_);
v_env_3052_ = lean_ctor_get(v___x_3051_, 0);
v_ngen_3053_ = lean_ctor_get(v___x_3051_, 2);
v_auxDeclNGen_3054_ = lean_ctor_get(v___x_3051_, 3);
v_traceState_3055_ = lean_ctor_get(v___x_3051_, 4);
v_cache_3056_ = lean_ctor_get(v___x_3051_, 5);
v_messages_3057_ = lean_ctor_get(v___x_3051_, 6);
v_infoState_3058_ = lean_ctor_get(v___x_3051_, 7);
v_snapshotTasks_3059_ = lean_ctor_get(v___x_3051_, 8);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___x_3051_, 1);
lean_dec(v_unused_3086_);
v___x_3061_ = v___x_3051_;
v_isShared_3062_ = v_isSharedCheck_3085_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_snapshotTasks_3059_);
lean_inc(v_infoState_3058_);
lean_inc(v_messages_3057_);
lean_inc(v_cache_3056_);
lean_inc(v_traceState_3055_);
lean_inc(v_auxDeclNGen_3054_);
lean_inc(v_ngen_3053_);
lean_inc(v_env_3052_);
lean_dec(v___x_3051_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3085_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 1, v_macroScope_3046_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_env_3052_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_macroScope_3046_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_ngen_3053_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_auxDeclNGen_3054_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_traceState_3055_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_cache_3056_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_messages_3057_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_infoState_3058_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_snapshotTasks_3059_);
v___x_3064_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_st_ref_set(v___y_3020_, v___x_3064_);
v___x_3066_ = l_List_reverse___redArg(v_traceMsgs_3047_);
v___x_3067_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3066_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3075_);
v___x_3069_ = v___x_3067_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v___x_3067_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_a_3045_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3045_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3045_);
v_a_3076_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3067_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3067_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_traceMsgs_3047_);
lean_dec(v_macroScope_3046_);
lean_dec(v_a_3045_);
v_a_3087_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3050_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3050_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; 
v_a_3095_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3043_, 2);
if (lean_obj_tag(v_a_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v_a_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_a_3096_ = lean_ctor_get(v_a_3095_, 0);
lean_inc(v_a_3096_);
v_a_3097_ = lean_ctor_get(v_a_3095_, 1);
lean_inc_ref(v_a_3097_);
lean_dec_ref_known(v_a_3095_, 2);
v___x_3098_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3099_ = lean_string_dec_eq(v_a_3097_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3097_);
v___x_3101_ = l_Lean_MessageData_ofFormat(v___x_3100_);
v___x_3102_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3096_, v___x_3101_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v_a_3096_);
return v___x_3102_;
}
else
{
lean_object* v___x_3103_; 
lean_dec_ref(v_a_3097_);
v___x_3103_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3096_);
return v___x_3103_;
}
}
else
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3106_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_quotContext_3119_; lean_object* v_currMacroScope_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_quotContext_3119_ = lean_ctor_get(v___y_3116_, 10);
lean_inc(v_quotContext_3119_);
v_currMacroScope_3120_ = lean_ctor_get(v___y_3116_, 11);
lean_inc(v_currMacroScope_3120_);
lean_dec_ref(v___y_3116_);
v___x_3121_ = l_Lean_addMacroScope(v_quotContext_3119_, v___x_3115_, v_currMacroScope_3120_);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___f_3136_; lean_object* v___x_3137_; 
v___f_3136_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3137_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3136_, v___y_3133_, v___y_3134_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3142_, uint8_t v_canonical_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3161_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3161_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = l_Lean_mkIdentFrom(v_ref_3142_, v_a_3153_, v_canonical_3143_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3152_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3152_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3170_, lean_object* v_canonical_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v_canonical_boxed_3180_; lean_object* v_res_3181_; 
v_canonical_boxed_3180_ = lean_unbox(v_canonical_3171_);
v_res_3181_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3170_, v_canonical_boxed_3180_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v_ref_3170_);
return v_res_3181_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3194_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3195_ = l_Lean_Name_append(v___x_3194_, v___x_3193_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3205_, lean_object* v_letOrReassign_3206_, lean_object* v_decl_3207_, lean_object* v_tk_3208_, lean_object* v_dec_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3205_, v_letOrReassign_3206_, v_decl_3207_, v_tk_3208_, v_dec_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec_ref(v_a_3210_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3219_, lean_object* v_letOrReassign_3220_, lean_object* v_decl_3221_, lean_object* v_tk_3222_, lean_object* v_dec_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3219_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref_known(v___x_3232_, 1);
lean_inc(v_decl_3221_);
v___x_3233_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3221_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v___x_3235_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3220_, v_a_3234_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v___x_3236_; 
lean_dec_ref_known(v___x_3235_, 1);
v___x_3236_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3223_, v_tk_3222_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3220_, v_decl_3221_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v_doBlockResultType_3240_; lean_object* v___x_3241_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v_doBlockResultType_3240_ = lean_ctor_get(v_a_3224_, 3);
lean_inc_ref(v_doBlockResultType_3240_);
v___x_3241_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3240_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3460_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3460_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3460_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3247_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3239_);
v___x_3250_ = l_Lean_Syntax_isOfKind(v_a_3239_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec(v_a_3239_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_tk_3222_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v___x_3251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v___x_3253_ = l_Lean_Syntax_getArg(v_a_3239_, v___x_3252_);
lean_dec(v_a_3239_);
v___x_3254_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3253_);
v___x_3255_ = l_Lean_Syntax_isOfKind(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
lean_dec(v_tk_3222_);
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3253_);
v___x_3257_ = l_Lean_Syntax_isOfKind(v___x_3253_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
v___x_3258_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3253_);
v___x_3259_ = l_Lean_Syntax_isOfKind(v___x_3253_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_dec(v___x_3253_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v___x_3260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; lean_object* v_id_3262_; lean_object* v_binders_3263_; lean_object* v_type_3264_; lean_object* v_value_3265_; lean_object* v___y_3267_; uint8_t v___y_3268_; uint8_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; uint8_t v___y_3279_; lean_object* v_id_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___x_3356_; 
v___x_3261_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3253_);
lean_dec(v___x_3253_);
v_id_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_id_3262_);
v_binders_3263_ = lean_ctor_get(v___x_3261_, 1);
lean_inc_ref(v_binders_3263_);
v_type_3264_ = lean_ctor_get(v___x_3261_, 2);
lean_inc(v_type_3264_);
v_value_3265_ = lean_ctor_get(v___x_3261_, 3);
lean_inc(v_value_3265_);
lean_dec_ref(v___x_3261_);
v___x_3356_ = l_Lean_Syntax_isIdent(v_id_3262_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3262_, v___x_3250_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
lean_dec(v_id_3262_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v_id_3338_ = v_a_3358_;
v___y_3339_ = v_a_3224_;
v___y_3340_ = v_a_3225_;
v___y_3341_ = v_a_3226_;
v___y_3342_ = v_a_3227_;
v___y_3343_ = v_a_3228_;
v___y_3344_ = v_a_3229_;
v___y_3345_ = v_a_3230_;
goto v___jp_3337_;
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_value_3265_);
lean_dec(v_type_3264_);
lean_dec_ref(v_binders_3263_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3359_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3357_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3357_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
v_id_3338_ = v_id_3262_;
v___y_3339_ = v_a_3224_;
v___y_3340_ = v_a_3225_;
v___y_3341_ = v_a_3226_;
v___y_3342_ = v_a_3227_;
v___y_3343_ = v_a_3228_;
v___y_3344_ = v_a_3229_;
v___y_3345_ = v_a_3230_;
goto v___jp_3337_;
}
v___jp_3266_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; 
v___x_3280_ = lean_box(v___x_3250_);
v___x_3281_ = lean_box(v___x_3255_);
v___x_3282_ = lean_box(v___y_3279_);
v___f_3283_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3283_, 0, v_type_3264_);
lean_closure_set(v___f_3283_, 1, v_value_3265_);
lean_closure_set(v___f_3283_, 2, v___x_3280_);
lean_closure_set(v___f_3283_, 3, v___x_3281_);
lean_closure_set(v___f_3283_, 4, v___x_3252_);
lean_closure_set(v___f_3283_, 5, v___x_3282_);
v___x_3284_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3263_, v___f_3283_, v___y_3278_, v___y_3277_, v___y_3276_, v___y_3275_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v_options_3286_; lean_object* v_fst_3287_; lean_object* v_snd_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3328_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v_options_3286_ = lean_ctor_get(v___y_3271_, 2);
v_fst_3287_ = lean_ctor_get(v_a_3285_, 0);
v_snd_3288_ = lean_ctor_get(v_a_3285_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_a_3285_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3290_ = v_a_3285_;
v_isShared_3291_ = v_isSharedCheck_3328_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_snd_3288_);
lean_inc(v_fst_3287_);
lean_dec(v_a_3285_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3328_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v_inheritedTraceOptions_3292_; uint8_t v_hasTrace_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v_inheritedTraceOptions_3292_ = lean_ctor_get(v___y_3271_, 13);
v_hasTrace_3293_ = lean_ctor_get_uint8(v_options_3286_, sizeof(void*)*1);
v___x_3294_ = lean_box(v___y_3269_);
v___x_3295_ = lean_box(v___y_3268_);
v___x_3296_ = lean_box(v___x_3255_);
v___x_3297_ = lean_box(v___y_3279_);
v___x_3298_ = lean_box(v___x_3250_);
lean_inc(v_snd_3288_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3299_, 0, v___y_3267_);
lean_closure_set(v___f_3299_, 1, v___y_3270_);
lean_closure_set(v___f_3299_, 2, v_a_3237_);
lean_closure_set(v___f_3299_, 3, v___x_3294_);
lean_closure_set(v___f_3299_, 4, v___x_3295_);
lean_closure_set(v___f_3299_, 5, v___x_3296_);
lean_closure_set(v___f_3299_, 6, v_snd_3288_);
lean_closure_set(v___f_3299_, 7, v___x_3297_);
lean_closure_set(v___f_3299_, 8, v___x_3298_);
lean_closure_set(v___f_3299_, 9, v_letOrReassign_3220_);
lean_closure_set(v___f_3299_, 10, v_a_3234_);
v___x_3300_ = l_Lean_Syntax_getId(v___y_3272_);
lean_dec(v___y_3272_);
v___x_3301_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3300_);
if (v_hasTrace_3293_ == 0)
{
lean_object* v___x_3302_; 
lean_del_object(v___x_3290_);
v___x_3302_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3300_, v_fst_3287_, v_snd_3288_, v___f_3299_, v___y_3279_, v___x_3301_, v___y_3274_, v___y_3278_, v___y_3277_, v___y_3276_, v___y_3275_, v___y_3271_, v___y_3273_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3303_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3304_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3292_, v_options_3286_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_del_object(v___x_3290_);
v___x_3306_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3300_, v_fst_3287_, v_snd_3288_, v___f_3299_, v___y_3279_, v___x_3301_, v___y_3274_, v___y_3278_, v___y_3277_, v___y_3276_, v___y_3275_, v___y_3271_, v___y_3273_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
lean_inc(v___x_3300_);
v___x_3307_ = l_Lean_MessageData_ofName(v___x_3300_);
v___x_3308_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 7);
lean_ctor_set(v___x_3290_, 1, v___x_3308_);
lean_ctor_set(v___x_3290_, 0, v___x_3307_);
v___x_3310_ = v___x_3290_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_inc(v_fst_3287_);
v___x_3311_ = l_Lean_MessageData_ofExpr(v_fst_3287_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
lean_inc(v_snd_3288_);
v___x_3315_ = l_Lean_MessageData_ofExpr(v_snd_3288_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3303_, v___x_3316_, v___y_3276_, v___y_3275_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref_known(v___x_3317_, 1);
v___x_3318_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3300_, v_fst_3287_, v_snd_3288_, v___f_3299_, v___y_3279_, v___x_3301_, v___y_3274_, v___y_3278_, v___y_3277_, v___y_3276_, v___y_3275_, v___y_3271_, v___y_3273_);
return v___x_3318_;
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v___x_3300_);
lean_dec_ref(v___f_3299_);
lean_dec(v_snd_3288_);
lean_dec(v_fst_3287_);
v_a_3319_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3317_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
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
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v___y_3272_);
lean_dec(v___y_3270_);
lean_dec(v___y_3267_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
v_a_3329_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3284_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3284_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
v___jp_3337_:
{
uint8_t v_nondep_3346_; 
v_nondep_3346_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1);
if (v_nondep_3346_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3220_) == 1)
{
uint8_t v_usedOnly_3347_; uint8_t v_zeta_3348_; lean_object* v_eq_x3f_3349_; 
v_usedOnly_3347_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 1);
v_zeta_3348_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 2);
v_eq_x3f_3349_ = lean_ctor_get(v_config_3219_, 0);
lean_inc(v_eq_x3f_3349_);
lean_dec_ref(v_config_3219_);
lean_inc(v_id_3338_);
v___y_3267_ = v_id_3338_;
v___y_3268_ = v_usedOnly_3347_;
v___y_3269_ = v_zeta_3348_;
v___y_3270_ = v_eq_x3f_3349_;
v___y_3271_ = v___y_3344_;
v___y_3272_ = v_id_3338_;
v___y_3273_ = v___y_3345_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___y_3343_;
v___y_3276_ = v___y_3342_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3340_;
v___y_3279_ = v___x_3250_;
goto v___jp_3266_;
}
else
{
uint8_t v_usedOnly_3350_; uint8_t v_zeta_3351_; lean_object* v_eq_x3f_3352_; 
v_usedOnly_3350_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 1);
v_zeta_3351_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 2);
v_eq_x3f_3352_ = lean_ctor_get(v_config_3219_, 0);
lean_inc(v_eq_x3f_3352_);
lean_dec_ref(v_config_3219_);
lean_inc(v_id_3338_);
v___y_3267_ = v_id_3338_;
v___y_3268_ = v_usedOnly_3350_;
v___y_3269_ = v_zeta_3351_;
v___y_3270_ = v_eq_x3f_3352_;
v___y_3271_ = v___y_3344_;
v___y_3272_ = v_id_3338_;
v___y_3273_ = v___y_3345_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___y_3343_;
v___y_3276_ = v___y_3342_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3340_;
v___y_3279_ = v_nondep_3346_;
goto v___jp_3266_;
}
}
else
{
uint8_t v_usedOnly_3353_; uint8_t v_zeta_3354_; lean_object* v_eq_x3f_3355_; 
v_usedOnly_3353_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 1);
v_zeta_3354_ = lean_ctor_get_uint8(v_config_3219_, sizeof(void*)*1 + 2);
v_eq_x3f_3355_ = lean_ctor_get(v_config_3219_, 0);
lean_inc(v_eq_x3f_3355_);
lean_dec_ref(v_config_3219_);
lean_inc(v_id_3338_);
v___y_3267_ = v_id_3338_;
v___y_3268_ = v_usedOnly_3353_;
v___y_3269_ = v_zeta_3354_;
v___y_3270_ = v_eq_x3f_3355_;
v___y_3271_ = v___y_3344_;
v___y_3272_ = v_id_3338_;
v___y_3273_ = v___y_3345_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___y_3343_;
v___y_3276_ = v___y_3342_;
v___y_3277_ = v___y_3341_;
v___y_3278_ = v___y_3340_;
v___y_3279_ = v___x_3250_;
goto v___jp_3266_;
}
}
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v___x_3368_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_3367_);
v___x_3369_ = l_Lean_Syntax_matchesNull(v___x_3368_, v___x_3252_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_dec(v___x_3253_);
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v___x_3370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3370_;
}
else
{
lean_object* v___x_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v_rhs_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v_xType_x3f_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3371_ = lean_box(v___x_3255_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3372_, 0, v___x_3371_);
v___x_3373_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_3252_);
v___x_3428_ = lean_unsigned_to_nat(2u);
v___x_3429_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_3428_);
v___x_3430_ = l_Lean_Syntax_isNone(v___x_3429_);
if (v___x_3430_ == 0)
{
uint8_t v___x_3431_; 
lean_inc(v___x_3429_);
v___x_3431_ = l_Lean_Syntax_matchesNull(v___x_3429_, v___x_3367_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
lean_dec(v___x_3429_);
lean_dec(v___x_3373_);
lean_dec_ref(v___f_3372_);
lean_dec(v___x_3253_);
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v___x_3432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3432_;
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3433_ = l_Lean_Syntax_getArg(v___x_3429_, v___x_3252_);
lean_dec(v___x_3429_);
v___x_3434_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3433_);
v___x_3435_ = l_Lean_Syntax_isOfKind(v___x_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; 
lean_dec(v___x_3433_);
lean_dec(v___x_3373_);
lean_dec_ref(v___f_3372_);
lean_dec(v___x_3253_);
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v___x_3436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3436_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = l_Lean_Syntax_getArg(v___x_3433_, v___x_3367_);
lean_dec(v___x_3433_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 1);
lean_ctor_set(v___x_3244_, 0, v___x_3437_);
v___x_3439_ = v___x_3244_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
v_xType_x3f_3394_ = v___x_3439_;
v___y_3395_ = v_a_3224_;
v___y_3396_ = v_a_3225_;
v___y_3397_ = v_a_3226_;
v___y_3398_ = v_a_3227_;
v___y_3399_ = v_a_3228_;
v___y_3400_ = v_a_3229_;
v___y_3401_ = v_a_3230_;
goto v___jp_3393_;
}
}
}
}
else
{
lean_object* v___x_3441_; 
lean_dec(v___x_3429_);
lean_del_object(v___x_3244_);
v___x_3441_ = lean_box(0);
v_xType_x3f_3394_ = v___x_3441_;
v___y_3395_ = v_a_3224_;
v___y_3396_ = v_a_3225_;
v___y_3397_ = v_a_3226_;
v___y_3398_ = v_a_3227_;
v___y_3399_ = v_a_3228_;
v___y_3400_ = v_a_3229_;
v___y_3401_ = v_a_3230_;
goto v___jp_3393_;
}
v___jp_3374_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3383_ = lean_box(v___x_3255_);
v___x_3384_ = lean_box(v___x_3250_);
lean_inc(v___x_3373_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3385_, 0, v_rhs_3375_);
lean_closure_set(v___f_3385_, 1, v___x_3383_);
lean_closure_set(v___f_3385_, 2, v_config_3219_);
lean_closure_set(v___f_3385_, 3, v_a_3242_);
lean_closure_set(v___f_3385_, 4, v___x_3384_);
lean_closure_set(v___f_3385_, 5, v___x_3246_);
lean_closure_set(v___f_3385_, 6, v___x_3247_);
lean_closure_set(v___f_3385_, 7, v___x_3248_);
lean_closure_set(v___f_3385_, 8, v___f_3372_);
lean_closure_set(v___f_3385_, 9, v___x_3373_);
v___x_3386_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3386_, 0, v_a_3237_);
v___x_3387_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3387_, 0, v_letOrReassign_3220_);
lean_closure_set(v___x_3387_, 1, v_a_3234_);
lean_closure_set(v___x_3387_, 2, v___x_3386_);
v___x_3388_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3389_ = l_Lean_MessageData_ofSyntax(v___x_3373_);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_box(0);
v___x_3392_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3390_, v___x_3387_, v___f_3385_, v___x_3391_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3392_;
}
v___jp_3393_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_unsigned_to_nat(4u);
v___x_3403_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_3402_);
lean_dec(v___x_3253_);
if (lean_obj_tag(v_xType_x3f_3394_) == 0)
{
v_rhs_3375_ = v___x_3403_;
v___y_3376_ = v___y_3395_;
v___y_3377_ = v___y_3396_;
v___y_3378_ = v___y_3397_;
v___y_3379_ = v___y_3398_;
v___y_3380_ = v___y_3399_;
v___y_3381_ = v___y_3400_;
v___y_3382_ = v___y_3401_;
goto v___jp_3374_;
}
else
{
lean_object* v_val_3404_; lean_object* v_ref_3405_; lean_object* v_quotContext_3406_; lean_object* v_currMacroScope_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_val_3404_ = lean_ctor_get(v_xType_x3f_3394_, 0);
lean_inc(v_val_3404_);
lean_dec_ref_known(v_xType_x3f_3394_, 1);
v_ref_3405_ = lean_ctor_get(v___y_3400_, 5);
v_quotContext_3406_ = lean_ctor_get(v___y_3400_, 10);
v_currMacroScope_3407_ = lean_ctor_get(v___y_3400_, 11);
v___x_3408_ = l_Lean_SourceInfo_fromRef(v_ref_3405_, v___x_3255_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3410_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3408_, 7);
v___x_3412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3408_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3414_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3415_ = lean_box(0);
lean_inc(v_currMacroScope_3407_);
lean_inc(v_quotContext_3406_);
v___x_3416_ = l_Lean_addMacroScope(v_quotContext_3406_, v___x_3415_, v_currMacroScope_3407_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3408_);
lean_ctor_set(v___x_3418_, 1, v___x_3414_);
lean_ctor_set(v___x_3418_, 2, v___x_3416_);
lean_ctor_set(v___x_3418_, 3, v___x_3417_);
v___x_3419_ = l_Lean_Syntax_node1(v___x_3408_, v___x_3413_, v___x_3418_);
v___x_3420_ = l_Lean_Syntax_node2(v___x_3408_, v___x_3410_, v___x_3412_, v___x_3419_);
v___x_3421_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3408_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3424_ = l_Lean_Syntax_node1(v___x_3408_, v___x_3423_, v_val_3404_);
v___x_3425_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3408_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_Syntax_node5(v___x_3408_, v___x_3409_, v___x_3420_, v___x_3403_, v___x_3422_, v___x_3424_, v___x_3426_);
v_rhs_3375_ = v___x_3427_;
v___y_3376_ = v___y_3395_;
v___y_3377_ = v___y_3396_;
v___y_3378_ = v___y_3397_;
v___y_3379_ = v___y_3398_;
v___y_3380_ = v___y_3399_;
v___y_3381_ = v___y_3400_;
v___y_3382_ = v___y_3401_;
goto v___jp_3374_;
}
}
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
lean_dec(v_a_3234_);
v___x_3442_ = lean_box(v___x_3250_);
lean_inc(v___x_3253_);
v___x_3443_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3443_, 0, v___x_3253_);
lean_closure_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3443_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v_ref_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v_ref_3446_ = lean_ctor_get(v_a_3229_, 5);
v___x_3447_ = 0;
v___x_3448_ = l_Lean_SourceInfo_fromRef(v_ref_3446_, v___x_3447_);
v___x_3449_ = l_Lean_Syntax_node1(v___x_3448_, v___x_3249_, v_a_3445_);
lean_inc(v___x_3449_);
v___x_3450_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3450_, 0, v_config_3219_);
lean_closure_set(v___x_3450_, 1, v_letOrReassign_3220_);
lean_closure_set(v___x_3450_, 2, v___x_3449_);
lean_closure_set(v___x_3450_, 3, v_tk_3222_);
lean_closure_set(v___x_3450_, 4, v_a_3237_);
v___x_3451_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3253_, v___x_3449_, v___x_3450_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
return v___x_3451_;
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___x_3253_);
lean_dec(v_a_3237_);
lean_dec(v_tk_3222_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3452_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3444_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3239_);
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_tk_3222_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
return v___x_3241_;
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3237_);
lean_dec(v_a_3234_);
lean_dec(v_tk_3222_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3461_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3238_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3238_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_a_3234_);
lean_dec(v_tk_3222_);
lean_dec(v_decl_3221_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3469_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3236_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3236_);
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
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_a_3234_);
lean_dec_ref(v_dec_3223_);
lean_dec(v_tk_3222_);
lean_dec(v_decl_3221_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3477_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3235_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3235_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_dec_3223_);
lean_dec(v_tk_3222_);
lean_dec(v_decl_3221_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3485_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3233_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3233_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_dec_3223_);
lean_dec(v_tk_3222_);
lean_dec(v_decl_3221_);
lean_dec(v_letOrReassign_3220_);
lean_dec_ref(v_config_3219_);
v_a_3493_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3232_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3232_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3501_, lean_object* v_x_3502_, lean_object* v_x_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3502_, v_x_3503_, v_x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3506_, lean_object* v_msg_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3506_, v_msg_3507_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3517_, lean_object* v_msg_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3517_, v_msg_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3519_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3533_, v___y_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v___y_3537_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3546_, lean_object* v_beforeStx_3547_, lean_object* v_afterStx_3548_, lean_object* v_x_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3547_, v_afterStx_3548_, v_x_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3559_, lean_object* v_beforeStx_3560_, lean_object* v_afterStx_3561_, lean_object* v_x_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3559_, v_beforeStx_3560_, v_afterStx_3561_, v_x_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v___y_3563_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3572_, lean_object* v_x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3573_, v___y_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_x_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3577_, v_x_3578_, v___y_3579_, v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_x_3578_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3582_, lean_object* v_ref_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3583_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3593_, lean_object* v_ref_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3593_, v_ref_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3615_, lean_object* v_x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3615_, v_x_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3626_, lean_object* v_x_3627_, size_t v_x_3628_, size_t v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3627_, v_x_3628_, v_x_3629_, v_x_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
size_t v_x_102776__boxed_3639_; size_t v_x_102777__boxed_3640_; lean_object* v_res_3641_; 
v_x_102776__boxed_3639_ = lean_unbox_usize(v_x_3635_);
lean_dec(v_x_3635_);
v_x_102777__boxed_3640_ = lean_unbox_usize(v_x_3636_);
lean_dec(v_x_3636_);
v_res_3641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3633_, v_x_3634_, v_x_102776__boxed_3639_, v_x_102777__boxed_3640_, v_x_3637_, v_x_3638_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3642_, lean_object* v_stx_3643_, lean_object* v_output_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3643_, v_output_3644_, v_x_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3654_, lean_object* v_stx_3655_, lean_object* v_output_3656_, lean_object* v_x_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3654_, v_stx_3655_, v_output_3656_, v_x_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3666_, lean_object* v_as_x27_3667_, lean_object* v_b_3668_, lean_object* v_a_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3667_, v_b_3668_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3679_, lean_object* v_as_x27_3680_, lean_object* v_b_3681_, lean_object* v_a_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3679_, v_as_x27_3680_, v_b_3681_, v_a_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v_as_x27_3680_);
lean_dec(v_as_3679_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3692_, lean_object* v_ref_3693_, lean_object* v_msg_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3693_, v_msg_3694_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3704_, lean_object* v_ref_3705_, lean_object* v_msg_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3704_, v_ref_3705_, v_msg_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v_ref_3705_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3716_, lean_object* v_n_3717_, lean_object* v_k_3718_, lean_object* v_v_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3717_, v_k_3718_, v_v_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3721_, size_t v_depth_3722_, lean_object* v_keys_3723_, lean_object* v_vals_3724_, lean_object* v_heq_3725_, lean_object* v_i_3726_, lean_object* v_entries_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3722_, v_keys_3723_, v_vals_3724_, v_i_3726_, v_entries_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3729_, lean_object* v_depth_3730_, lean_object* v_keys_3731_, lean_object* v_vals_3732_, lean_object* v_heq_3733_, lean_object* v_i_3734_, lean_object* v_entries_3735_){
_start:
{
size_t v_depth_boxed_3736_; lean_object* v_res_3737_; 
v_depth_boxed_3736_ = lean_unbox_usize(v_depth_3730_);
lean_dec(v_depth_3730_);
v_res_3737_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3729_, v_depth_boxed_3736_, v_keys_3731_, v_vals_3732_, v_heq_3733_, v_i_3734_, v_entries_3735_);
lean_dec_ref(v_vals_3732_);
lean_dec_ref(v_keys_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3754_, lean_object* v_x_3755_, lean_object* v_mkInfoTree_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3755_, v_mkInfoTree_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3765_, lean_object* v_x_3766_, lean_object* v_mkInfoTree_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3765_, v_x_3766_, v_mkInfoTree_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3776_, lean_object* v_m_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3777_, v_a_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3780_, lean_object* v_m_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3780_, v_m_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_m_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_, lean_object* v_x_3787_, lean_object* v_x_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3785_, v_x_3786_, v_x_3787_, v_x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3791_, v_x_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
uint8_t v_res_3797_; lean_object* v_r_3798_; 
v_res_3797_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3794_, v_x_3795_, v_x_3796_);
lean_dec_ref(v_x_3796_);
lean_dec_ref(v_x_3795_);
v_r_3798_ = lean_box(v_res_3797_);
return v_r_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3799_, lean_object* v_a_3800_, lean_object* v_x_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_3800_, v_x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3803_, lean_object* v_a_3804_, lean_object* v_x_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3803_, v_a_3804_, v_x_3805_);
lean_dec(v_x_3805_);
lean_dec(v_a_3804_);
return v_res_3806_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3807_, lean_object* v_x_3808_, size_t v_x_3809_, lean_object* v_x_3810_){
_start:
{
uint8_t v___x_3811_; 
v___x_3811_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3808_, v_x_3809_, v_x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_, lean_object* v_x_3815_){
_start:
{
size_t v_x_102946__boxed_3816_; uint8_t v_res_3817_; lean_object* v_r_3818_; 
v_x_102946__boxed_3816_ = lean_unbox_usize(v_x_3814_);
lean_dec(v_x_3814_);
v_res_3817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3812_, v_x_3813_, v_x_102946__boxed_3816_, v_x_3815_);
lean_dec_ref(v_x_3815_);
lean_dec_ref(v_x_3813_);
v_r_3818_ = lean_box(v_res_3817_);
return v_r_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3819_, lean_object* v_keys_3820_, lean_object* v_vals_3821_, lean_object* v_heq_3822_, lean_object* v_i_3823_, lean_object* v_k_3824_){
_start:
{
uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3820_, v_i_3823_, v_k_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3826_, lean_object* v_keys_3827_, lean_object* v_vals_3828_, lean_object* v_heq_3829_, lean_object* v_i_3830_, lean_object* v_k_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3826_, v_keys_3827_, v_vals_3828_, v_heq_3829_, v_i_3830_, v_k_3831_);
lean_dec_ref(v_k_3831_);
lean_dec_ref(v_vals_3828_);
lean_dec_ref(v_keys_3827_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3843_, lean_object* v_otherwise_x3f_3844_, uint8_t v___x_3845_, lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v_dec_3851_, uint8_t v___x_3852_, lean_object* v___y_3853_, lean_object* v___x_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; uint8_t v___y_3886_; 
switch(lean_obj_tag(v_letOrReassign_3843_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3844_) == 1)
{
lean_object* v_mutTk_x3f_3897_; lean_object* v_val_3898_; lean_object* v_ref_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3929_; 
v_mutTk_x3f_3897_ = lean_ctor_get(v_letOrReassign_3843_, 0);
v_val_3898_ = lean_ctor_get(v_otherwise_x3f_3844_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v_otherwise_x3f_3844_, 1);
v_ref_3899_ = lean_ctor_get(v___y_3860_, 5);
v___x_3900_ = l_Lean_SourceInfo_fromRef(v_ref_3899_, v___x_3845_);
v___x_3901_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3848_);
lean_inc_ref(v___x_3847_);
lean_inc_ref(v___x_3846_);
v___x_3902_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3901_);
v___x_3903_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3900_);
v___x_3904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3900_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3906_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3897_) == 1)
{
lean_object* v_val_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_val_3944_ = lean_ctor_get(v_mutTk_x3f_3897_, 0);
v___x_3945_ = l_Lean_SourceInfo_fromRef(v_val_3944_, v___x_3852_);
v___x_3946_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l_Array_mkArray1___redArg(v___x_3947_);
v___y_3929_ = v___x_3948_;
goto v___jp_3928_;
}
else
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_mk_empty_array_with_capacity(v___x_3854_);
v___y_3929_ = v___x_3949_;
goto v___jp_3928_;
}
v___jp_3907_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3913_ = l_Array_append___redArg(v___x_3906_, v___y_3912_);
lean_dec_ref(v___y_3912_);
lean_inc(v___x_3900_);
v___x_3914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3900_);
lean_ctor_set(v___x_3914_, 1, v___x_3905_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
v___x_3915_ = lean_unsigned_to_nat(9u);
v___x_3916_ = lean_mk_empty_array_with_capacity(v___x_3915_);
v___x_3917_ = lean_array_push(v___x_3916_, v___x_3904_);
v___x_3918_ = lean_array_push(v___x_3917_, v___y_3911_);
v___x_3919_ = lean_array_push(v___x_3918_, v___y_3910_);
v___x_3920_ = lean_array_push(v___x_3919_, v___x_3849_);
v___x_3921_ = lean_array_push(v___x_3920_, v___y_3909_);
v___x_3922_ = lean_array_push(v___x_3921_, v___x_3850_);
v___x_3923_ = lean_array_push(v___x_3922_, v___y_3908_);
v___x_3924_ = lean_array_push(v___x_3923_, v_val_3898_);
v___x_3925_ = lean_array_push(v___x_3924_, v___x_3914_);
v___x_3926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3900_);
lean_ctor_set(v___x_3926_, 1, v___x_3902_);
lean_ctor_set(v___x_3926_, 2, v___x_3925_);
v___x_3927_ = l_Lean_Elab_Do_elabDoElem(v___x_3926_, v_dec_3851_, v___x_3852_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3927_;
}
v___jp_3928_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3930_ = l_Array_append___redArg(v___x_3906_, v___y_3929_);
lean_dec_ref(v___y_3929_);
lean_inc_n(v___x_3900_, 5);
v___x_3931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3900_);
lean_ctor_set(v___x_3931_, 1, v___x_3905_);
lean_ctor_set(v___x_3931_, 2, v___x_3930_);
v___x_3932_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3933_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3932_);
v___x_3934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3900_);
lean_ctor_set(v___x_3934_, 1, v___x_3905_);
lean_ctor_set(v___x_3934_, 2, v___x_3906_);
v___x_3935_ = l_Lean_Syntax_node1(v___x_3900_, v___x_3933_, v___x_3934_);
v___x_3936_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3900_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_3939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3900_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
if (lean_obj_tag(v___y_3853_) == 0)
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_mk_empty_array_with_capacity(v___x_3854_);
v___y_3908_ = v___x_3939_;
v___y_3909_ = v___x_3937_;
v___y_3910_ = v___x_3935_;
v___y_3911_ = v___x_3931_;
v___y_3912_ = v___x_3940_;
goto v___jp_3907_;
}
else
{
lean_object* v_val_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_val_3941_ = lean_ctor_get(v___y_3853_, 0);
lean_inc(v_val_3941_);
lean_dec_ref_known(v___y_3853_, 1);
v___x_3942_ = lean_mk_empty_array_with_capacity(v___x_3854_);
v___x_3943_ = lean_array_push(v___x_3942_, v_val_3941_);
v___y_3908_ = v___x_3939_;
v___y_3909_ = v___x_3937_;
v___y_3910_ = v___x_3935_;
v___y_3911_ = v___x_3931_;
v___y_3912_ = v___x_3943_;
goto v___jp_3907_;
}
}
}
else
{
lean_object* v_mutTk_x3f_3950_; lean_object* v_ref_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___y_3960_; 
lean_dec(v___y_3853_);
lean_dec(v_otherwise_x3f_3844_);
v_mutTk_x3f_3950_ = lean_ctor_get(v_letOrReassign_3843_, 0);
v_ref_3951_ = lean_ctor_get(v___y_3860_, 5);
v___x_3952_ = l_Lean_SourceInfo_fromRef(v_ref_3951_, v___x_3845_);
v___x_3953_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3848_);
lean_inc_ref(v___x_3847_);
lean_inc_ref(v___x_3846_);
v___x_3954_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3953_);
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_3952_);
v___x_3956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3952_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3958_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_3950_) == 1)
{
lean_object* v_val_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v_val_3977_ = lean_ctor_get(v_mutTk_x3f_3950_, 0);
v___x_3978_ = l_Lean_SourceInfo_fromRef(v_val_3977_, v___x_3852_);
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_3980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3978_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = l_Array_mkArray1___redArg(v___x_3980_);
v___y_3960_ = v___x_3981_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_mk_empty_array_with_capacity(v___x_3854_);
v___y_3960_ = v___x_3982_;
goto v___jp_3959_;
}
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3961_ = l_Array_append___redArg(v___x_3958_, v___y_3960_);
lean_dec_ref(v___y_3960_);
lean_inc_n(v___x_3952_, 6);
v___x_3962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3952_);
lean_ctor_set(v___x_3962_, 1, v___x_3957_);
lean_ctor_set(v___x_3962_, 2, v___x_3961_);
v___x_3963_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3848_, 2);
lean_inc_ref_n(v___x_3847_, 2);
lean_inc_ref_n(v___x_3846_, 2);
v___x_3964_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3963_);
v___x_3965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3952_);
lean_ctor_set(v___x_3965_, 1, v___x_3957_);
lean_ctor_set(v___x_3965_, 2, v___x_3958_);
lean_inc_ref_n(v___x_3965_, 2);
v___x_3966_ = l_Lean_Syntax_node1(v___x_3952_, v___x_3964_, v___x_3965_);
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3968_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3967_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3970_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3969_);
v___x_3971_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3952_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = l_Lean_Syntax_node5(v___x_3952_, v___x_3970_, v___x_3849_, v___x_3965_, v___x_3965_, v___x_3972_, v___x_3850_);
v___x_3974_ = l_Lean_Syntax_node1(v___x_3952_, v___x_3968_, v___x_3973_);
v___x_3975_ = l_Lean_Syntax_node4(v___x_3952_, v___x_3954_, v___x_3956_, v___x_3962_, v___x_3966_, v___x_3974_);
v___x_3976_ = l_Lean_Elab_Do_elabDoElem(v___x_3975_, v_dec_3851_, v___x_3852_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3976_;
}
}
}
case 1:
{
lean_dec(v___y_3853_);
if (lean_obj_tag(v_otherwise_x3f_3844_) == 1)
{
lean_object* v___x_3983_; 
lean_dec_ref_known(v_otherwise_x3f_3844_, 1);
lean_dec_ref(v_dec_3851_);
lean_dec(v___x_3850_);
lean_dec(v___x_3849_);
lean_dec_ref(v___x_3848_);
lean_dec_ref(v___x_3847_);
lean_dec_ref(v___x_3846_);
v___x_3983_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3983_;
}
else
{
lean_object* v_ref_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec(v_otherwise_x3f_3844_);
v_ref_3984_ = lean_ctor_get(v___y_3860_, 5);
v___x_3985_ = l_Lean_SourceInfo_fromRef(v_ref_3984_, v___x_3845_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3848_, 3);
lean_inc_ref_n(v___x_3847_, 3);
lean_inc_ref_n(v___x_3846_, 3);
v___x_3987_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3986_);
v___x_3988_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_3985_, 6);
v___x_3989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3985_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_3991_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3990_);
v___x_3992_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3993_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_3994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3985_);
lean_ctor_set(v___x_3994_, 1, v___x_3992_);
lean_ctor_set(v___x_3994_, 2, v___x_3993_);
lean_inc_ref_n(v___x_3994_, 2);
v___x_3995_ = l_Lean_Syntax_node1(v___x_3985_, v___x_3991_, v___x_3994_);
v___x_3996_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_3997_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3996_);
v___x_3998_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3999_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3985_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node5(v___x_3985_, v___x_3999_, v___x_3849_, v___x_3994_, v___x_3994_, v___x_4001_, v___x_3850_);
v___x_4003_ = l_Lean_Syntax_node1(v___x_3985_, v___x_3997_, v___x_4002_);
v___x_4004_ = l_Lean_Syntax_node3(v___x_3985_, v___x_3987_, v___x_3989_, v___x_3995_, v___x_4003_);
v___x_4005_ = l_Lean_Elab_Do_elabDoElem(v___x_4004_, v_dec_3851_, v___x_3852_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_4005_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3844_);
if (lean_obj_tag(v___y_3853_) == 0)
{
v___y_3886_ = v___x_3852_;
goto v___jp_3885_;
}
else
{
lean_dec_ref_known(v___y_3853_, 1);
v___y_3886_ = v___x_3845_;
goto v___jp_3885_;
}
}
}
v___jp_3863_:
{
lean_object* v_ref_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_ref_3871_ = lean_ctor_get(v___y_3869_, 5);
v___x_3872_ = l_Lean_SourceInfo_fromRef(v_ref_3871_, v___x_3845_);
v___x_3873_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3848_);
lean_inc_ref(v___x_3847_);
lean_inc_ref(v___x_3846_);
v___x_3874_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3873_);
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_3876_ = l_Lean_Name_mkStr4(v___x_3846_, v___x_3847_, v___x_3848_, v___x_3875_);
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3878_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_3872_, 3);
v___x_3879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3872_);
lean_ctor_set(v___x_3879_, 1, v___x_3877_);
lean_ctor_set(v___x_3879_, 2, v___x_3878_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_3881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3872_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
lean_inc_ref(v___x_3879_);
v___x_3882_ = l_Lean_Syntax_node5(v___x_3872_, v___x_3876_, v___x_3849_, v___x_3879_, v___x_3879_, v___x_3881_, v___x_3850_);
v___x_3883_ = l_Lean_Syntax_node1(v___x_3872_, v___x_3874_, v___x_3882_);
v___x_3884_ = l_Lean_Elab_Do_elabDoElem(v___x_3883_, v_dec_3851_, v___x_3852_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
return v___x_3884_;
}
v___jp_3885_:
{
if (v___y_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_dec_3851_);
lean_dec(v___x_3850_);
lean_dec(v___x_3849_);
lean_dec_ref(v___x_3848_);
lean_dec_ref(v___x_3847_);
lean_dec_ref(v___x_3846_);
v___x_3887_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_3888_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_3887_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3888_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
v___y_3864_ = v___y_3855_;
v___y_3865_ = v___y_3856_;
v___y_3866_ = v___y_3857_;
v___y_3867_ = v___y_3858_;
v___y_3868_ = v___y_3859_;
v___y_3869_ = v___y_3860_;
v___y_3870_ = v___y_3861_;
goto v___jp_3863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4006_ = _args[0];
lean_object* v_otherwise_x3f_4007_ = _args[1];
lean_object* v___x_4008_ = _args[2];
lean_object* v___x_4009_ = _args[3];
lean_object* v___x_4010_ = _args[4];
lean_object* v___x_4011_ = _args[5];
lean_object* v___x_4012_ = _args[6];
lean_object* v___x_4013_ = _args[7];
lean_object* v_dec_4014_ = _args[8];
lean_object* v___x_4015_ = _args[9];
lean_object* v___y_4016_ = _args[10];
lean_object* v___x_4017_ = _args[11];
lean_object* v___y_4018_ = _args[12];
lean_object* v___y_4019_ = _args[13];
lean_object* v___y_4020_ = _args[14];
lean_object* v___y_4021_ = _args[15];
lean_object* v___y_4022_ = _args[16];
lean_object* v___y_4023_ = _args[17];
lean_object* v___y_4024_ = _args[18];
lean_object* v___y_4025_ = _args[19];
_start:
{
uint8_t v___x_39001__boxed_4026_; uint8_t v___x_39007__boxed_4027_; lean_object* v_res_4028_; 
v___x_39001__boxed_4026_ = lean_unbox(v___x_4008_);
v___x_39007__boxed_4027_ = lean_unbox(v___x_4015_);
v_res_4028_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4006_, v_otherwise_x3f_4007_, v___x_39001__boxed_4026_, v___x_4009_, v___x_4010_, v___x_4011_, v___x_4012_, v___x_4013_, v_dec_4014_, v___x_39007__boxed_4027_, v___y_4016_, v___x_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___x_4017_);
lean_dec(v_letOrReassign_4006_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4029_, lean_object* v_otherwise_x3f_4030_, uint8_t v___x_4031_, lean_object* v___x_4032_, lean_object* v___x_4033_, lean_object* v___x_4034_, lean_object* v___x_4035_, lean_object* v___x_4036_, lean_object* v_dec_4037_, uint8_t v___x_4038_, lean_object* v___y_4039_, lean_object* v___x_4040_, uint8_t v___x_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; uint8_t v___y_4073_; 
switch(lean_obj_tag(v_letOrReassign_4029_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4030_) == 1)
{
lean_object* v_mutTk_x3f_4084_; lean_object* v_val_4085_; lean_object* v_ref_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4116_; 
v_mutTk_x3f_4084_ = lean_ctor_get(v_letOrReassign_4029_, 0);
v_val_4085_ = lean_ctor_get(v_otherwise_x3f_4030_, 0);
lean_inc(v_val_4085_);
lean_dec_ref_known(v_otherwise_x3f_4030_, 1);
v_ref_4086_ = lean_ctor_get(v___y_4047_, 5);
v___x_4087_ = l_Lean_SourceInfo_fromRef(v_ref_4086_, v___x_4031_);
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4034_);
lean_inc_ref(v___x_4033_);
lean_inc_ref(v___x_4032_);
v___x_4089_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4088_);
v___x_4090_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4087_);
v___x_4091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4087_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4093_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4084_) == 1)
{
lean_object* v_val_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_val_4131_ = lean_ctor_get(v_mutTk_x3f_4084_, 0);
v___x_4132_ = l_Lean_SourceInfo_fromRef(v_val_4131_, v___x_4038_);
v___x_4133_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Array_mkArray1___redArg(v___x_4134_);
v___y_4116_ = v___x_4135_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_mk_empty_array_with_capacity(v___x_4040_);
v___y_4116_ = v___x_4136_;
goto v___jp_4115_;
}
v___jp_4094_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4100_ = l_Array_append___redArg(v___x_4093_, v___y_4099_);
lean_dec_ref(v___y_4099_);
lean_inc(v___x_4087_);
v___x_4101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4087_);
lean_ctor_set(v___x_4101_, 1, v___x_4092_);
lean_ctor_set(v___x_4101_, 2, v___x_4100_);
v___x_4102_ = lean_unsigned_to_nat(9u);
v___x_4103_ = lean_mk_empty_array_with_capacity(v___x_4102_);
v___x_4104_ = lean_array_push(v___x_4103_, v___x_4091_);
v___x_4105_ = lean_array_push(v___x_4104_, v___y_4096_);
v___x_4106_ = lean_array_push(v___x_4105_, v___y_4095_);
v___x_4107_ = lean_array_push(v___x_4106_, v___x_4035_);
v___x_4108_ = lean_array_push(v___x_4107_, v___y_4098_);
v___x_4109_ = lean_array_push(v___x_4108_, v___x_4036_);
v___x_4110_ = lean_array_push(v___x_4109_, v___y_4097_);
v___x_4111_ = lean_array_push(v___x_4110_, v_val_4085_);
v___x_4112_ = lean_array_push(v___x_4111_, v___x_4101_);
v___x_4113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4087_);
lean_ctor_set(v___x_4113_, 1, v___x_4089_);
lean_ctor_set(v___x_4113_, 2, v___x_4112_);
v___x_4114_ = l_Lean_Elab_Do_elabDoElem(v___x_4113_, v_dec_4037_, v___x_4038_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4114_;
}
v___jp_4115_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4117_ = l_Array_append___redArg(v___x_4093_, v___y_4116_);
lean_dec_ref(v___y_4116_);
lean_inc_n(v___x_4087_, 5);
v___x_4118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4087_);
lean_ctor_set(v___x_4118_, 1, v___x_4092_);
lean_ctor_set(v___x_4118_, 2, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4120_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4087_);
lean_ctor_set(v___x_4121_, 1, v___x_4092_);
lean_ctor_set(v___x_4121_, 2, v___x_4093_);
v___x_4122_ = l_Lean_Syntax_node1(v___x_4087_, v___x_4120_, v___x_4121_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4087_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4087_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
if (lean_obj_tag(v___y_4039_) == 0)
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_mk_empty_array_with_capacity(v___x_4040_);
v___y_4095_ = v___x_4122_;
v___y_4096_ = v___x_4118_;
v___y_4097_ = v___x_4126_;
v___y_4098_ = v___x_4124_;
v___y_4099_ = v___x_4127_;
goto v___jp_4094_;
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_val_4128_ = lean_ctor_get(v___y_4039_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v___y_4039_, 1);
v___x_4129_ = lean_mk_empty_array_with_capacity(v___x_4040_);
v___x_4130_ = lean_array_push(v___x_4129_, v_val_4128_);
v___y_4095_ = v___x_4122_;
v___y_4096_ = v___x_4118_;
v___y_4097_ = v___x_4126_;
v___y_4098_ = v___x_4124_;
v___y_4099_ = v___x_4130_;
goto v___jp_4094_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4137_; lean_object* v_ref_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___y_4147_; 
lean_dec(v___y_4039_);
lean_dec(v_otherwise_x3f_4030_);
v_mutTk_x3f_4137_ = lean_ctor_get(v_letOrReassign_4029_, 0);
v_ref_4138_ = lean_ctor_get(v___y_4047_, 5);
v___x_4139_ = l_Lean_SourceInfo_fromRef(v_ref_4138_, v___x_4031_);
v___x_4140_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4034_);
lean_inc_ref(v___x_4033_);
lean_inc_ref(v___x_4032_);
v___x_4141_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4140_);
v___x_4142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4139_);
v___x_4143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4139_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4145_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4137_) == 1)
{
lean_object* v_val_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_val_4164_ = lean_ctor_get(v_mutTk_x3f_4137_, 0);
v___x_4165_ = l_Lean_SourceInfo_fromRef(v_val_4164_, v___x_4038_);
v___x_4166_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Array_mkArray1___redArg(v___x_4167_);
v___y_4147_ = v___x_4168_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_mk_empty_array_with_capacity(v___x_4040_);
v___y_4147_ = v___x_4169_;
goto v___jp_4146_;
}
v___jp_4146_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4148_ = l_Array_append___redArg(v___x_4145_, v___y_4147_);
lean_dec_ref(v___y_4147_);
lean_inc_n(v___x_4139_, 6);
v___x_4149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4139_);
lean_ctor_set(v___x_4149_, 1, v___x_4144_);
lean_ctor_set(v___x_4149_, 2, v___x_4148_);
v___x_4150_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4034_, 2);
lean_inc_ref_n(v___x_4033_, 2);
lean_inc_ref_n(v___x_4032_, 2);
v___x_4151_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4150_);
v___x_4152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4139_);
lean_ctor_set(v___x_4152_, 1, v___x_4144_);
lean_ctor_set(v___x_4152_, 2, v___x_4145_);
lean_inc_ref_n(v___x_4152_, 2);
v___x_4153_ = l_Lean_Syntax_node1(v___x_4139_, v___x_4151_, v___x_4152_);
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4155_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4154_);
v___x_4156_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4157_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4156_);
v___x_4158_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4139_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l_Lean_Syntax_node5(v___x_4139_, v___x_4157_, v___x_4035_, v___x_4152_, v___x_4152_, v___x_4159_, v___x_4036_);
v___x_4161_ = l_Lean_Syntax_node1(v___x_4139_, v___x_4155_, v___x_4160_);
v___x_4162_ = l_Lean_Syntax_node4(v___x_4139_, v___x_4141_, v___x_4143_, v___x_4149_, v___x_4153_, v___x_4161_);
v___x_4163_ = l_Lean_Elab_Do_elabDoElem(v___x_4162_, v_dec_4037_, v___x_4038_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4163_;
}
}
}
case 1:
{
lean_dec(v___y_4039_);
if (lean_obj_tag(v_otherwise_x3f_4030_) == 1)
{
lean_object* v___x_4170_; 
lean_dec_ref_known(v_otherwise_x3f_4030_, 1);
lean_dec_ref(v_dec_4037_);
lean_dec(v___x_4036_);
lean_dec(v___x_4035_);
lean_dec_ref(v___x_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v___x_4032_);
v___x_4170_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4170_;
}
else
{
lean_object* v_ref_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_dec(v_otherwise_x3f_4030_);
v_ref_4171_ = lean_ctor_get(v___y_4047_, 5);
v___x_4172_ = l_Lean_SourceInfo_fromRef(v_ref_4171_, v___x_4031_);
v___x_4173_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4034_, 3);
lean_inc_ref_n(v___x_4033_, 3);
lean_inc_ref_n(v___x_4032_, 3);
v___x_4174_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4173_);
v___x_4175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4172_, 6);
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4172_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4178_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4180_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4172_);
lean_ctor_set(v___x_4181_, 1, v___x_4179_);
lean_ctor_set(v___x_4181_, 2, v___x_4180_);
lean_inc_ref_n(v___x_4181_, 2);
v___x_4182_ = l_Lean_Syntax_node1(v___x_4172_, v___x_4178_, v___x_4181_);
v___x_4183_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4184_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4183_);
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4186_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4185_);
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4172_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = l_Lean_Syntax_node5(v___x_4172_, v___x_4186_, v___x_4035_, v___x_4181_, v___x_4181_, v___x_4188_, v___x_4036_);
v___x_4190_ = l_Lean_Syntax_node1(v___x_4172_, v___x_4184_, v___x_4189_);
v___x_4191_ = l_Lean_Syntax_node3(v___x_4172_, v___x_4174_, v___x_4176_, v___x_4182_, v___x_4190_);
v___x_4192_ = l_Lean_Elab_Do_elabDoElem(v___x_4191_, v_dec_4037_, v___x_4038_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4192_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4030_);
if (lean_obj_tag(v___y_4039_) == 0)
{
v___y_4073_ = v___x_4041_;
goto v___jp_4072_;
}
else
{
lean_dec_ref_known(v___y_4039_, 1);
v___y_4073_ = v___x_4031_;
goto v___jp_4072_;
}
}
}
v___jp_4050_:
{
lean_object* v_ref_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_ref_4058_ = lean_ctor_get(v___y_4056_, 5);
v___x_4059_ = l_Lean_SourceInfo_fromRef(v_ref_4058_, v___x_4031_);
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4034_);
lean_inc_ref(v___x_4033_);
lean_inc_ref(v___x_4032_);
v___x_4061_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4060_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4063_ = l_Lean_Name_mkStr4(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4062_);
v___x_4064_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4065_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4059_, 3);
v___x_4066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4059_);
lean_ctor_set(v___x_4066_, 1, v___x_4064_);
lean_ctor_set(v___x_4066_, 2, v___x_4065_);
v___x_4067_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4059_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
lean_inc_ref(v___x_4066_);
v___x_4069_ = l_Lean_Syntax_node5(v___x_4059_, v___x_4063_, v___x_4035_, v___x_4066_, v___x_4066_, v___x_4068_, v___x_4036_);
v___x_4070_ = l_Lean_Syntax_node1(v___x_4059_, v___x_4061_, v___x_4069_);
v___x_4071_ = l_Lean_Elab_Do_elabDoElem(v___x_4070_, v_dec_4037_, v___x_4038_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
return v___x_4071_;
}
v___jp_4072_:
{
if (v___y_4073_ == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref(v_dec_4037_);
lean_dec(v___x_4036_);
lean_dec(v___x_4035_);
lean_dec_ref(v___x_4034_);
lean_dec_ref(v___x_4033_);
lean_dec_ref(v___x_4032_);
v___x_4074_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4075_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4074_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
v___y_4051_ = v___y_4042_;
v___y_4052_ = v___y_4043_;
v___y_4053_ = v___y_4044_;
v___y_4054_ = v___y_4045_;
v___y_4055_ = v___y_4046_;
v___y_4056_ = v___y_4047_;
v___y_4057_ = v___y_4048_;
goto v___jp_4050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4193_ = _args[0];
lean_object* v_otherwise_x3f_4194_ = _args[1];
lean_object* v___x_4195_ = _args[2];
lean_object* v___x_4196_ = _args[3];
lean_object* v___x_4197_ = _args[4];
lean_object* v___x_4198_ = _args[5];
lean_object* v___x_4199_ = _args[6];
lean_object* v___x_4200_ = _args[7];
lean_object* v_dec_4201_ = _args[8];
lean_object* v___x_4202_ = _args[9];
lean_object* v___y_4203_ = _args[10];
lean_object* v___x_4204_ = _args[11];
lean_object* v___x_4205_ = _args[12];
lean_object* v___y_4206_ = _args[13];
lean_object* v___y_4207_ = _args[14];
lean_object* v___y_4208_ = _args[15];
lean_object* v___y_4209_ = _args[16];
lean_object* v___y_4210_ = _args[17];
lean_object* v___y_4211_ = _args[18];
lean_object* v___y_4212_ = _args[19];
lean_object* v___y_4213_ = _args[20];
_start:
{
uint8_t v___x_39383__boxed_4214_; uint8_t v___x_39389__boxed_4215_; uint8_t v___x_39392__boxed_4216_; lean_object* v_res_4217_; 
v___x_39383__boxed_4214_ = lean_unbox(v___x_4195_);
v___x_39389__boxed_4215_ = lean_unbox(v___x_4202_);
v___x_39392__boxed_4216_ = lean_unbox(v___x_4205_);
v_res_4217_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4193_, v_otherwise_x3f_4194_, v___x_39383__boxed_4214_, v___x_4196_, v___x_4197_, v___x_4198_, v___x_4199_, v___x_4200_, v_dec_4201_, v___x_39389__boxed_4215_, v___y_4203_, v___x_4204_, v___x_39392__boxed_4216_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___x_4204_);
lean_dec(v_letOrReassign_4193_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4238_, lean_object* v_stx_4239_, lean_object* v_tk_4240_, lean_object* v_dec_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4252_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4253_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4239_);
v___x_4254_ = l_Lean_Syntax_isOfKind(v_stx_4239_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; uint8_t v___x_4256_; 
v___x_4255_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4239_);
v___x_4256_ = l_Lean_Syntax_isOfKind(v_stx_4239_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; 
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4257_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4257_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; 
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4258_);
v___x_4260_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4259_);
v___x_4261_ = l_Lean_Syntax_isOfKind(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4347_; lean_object* v_patType_x3f_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___x_4378_; uint8_t v___x_4379_; 
v___x_4347_ = lean_unsigned_to_nat(1u);
v___x_4378_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4347_);
v___x_4379_ = l_Lean_Syntax_isNone(v___x_4378_);
if (v___x_4379_ == 0)
{
uint8_t v___x_4380_; 
lean_inc(v___x_4378_);
v___x_4380_ = l_Lean_Syntax_matchesNull(v___x_4378_, v___x_4347_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; 
lean_dec(v___x_4378_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4382_ = l_Lean_Syntax_getArg(v___x_4378_, v___x_4258_);
lean_dec(v___x_4378_);
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4382_);
v___x_4384_ = l_Lean_Syntax_isOfKind(v___x_4382_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
lean_dec(v___x_4382_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4385_;
}
else
{
lean_object* v_patType_x3f_4386_; lean_object* v___x_4387_; 
v_patType_x3f_4386_ = l_Lean_Syntax_getArg(v___x_4382_, v___x_4347_);
lean_dec(v___x_4382_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v_patType_x3f_4386_);
v_patType_x3f_4349_ = v___x_4387_;
v___y_4350_ = v_a_4242_;
v___y_4351_ = v_a_4243_;
v___y_4352_ = v_a_4244_;
v___y_4353_ = v_a_4245_;
v___y_4354_ = v_a_4246_;
v___y_4355_ = v_a_4247_;
v___y_4356_ = v_a_4248_;
goto v___jp_4348_;
}
}
}
else
{
lean_object* v___x_4388_; 
lean_dec(v___x_4378_);
v___x_4388_ = lean_box(0);
v_patType_x3f_4349_ = v___x_4388_;
v___y_4350_ = v_a_4242_;
v___y_4351_ = v_a_4243_;
v___y_4352_ = v_a_4244_;
v___y_4353_ = v_a_4245_;
v___y_4354_ = v_a_4246_;
v___y_4355_ = v_a_4247_;
v___y_4356_ = v_a_4248_;
goto v___jp_4348_;
}
v___jp_4348_:
{
lean_object* v___x_4357_; lean_object* v_rhs_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4357_ = lean_unsigned_to_nat(3u);
v_rhs_4358_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4357_);
v___x_4359_ = lean_unsigned_to_nat(4u);
v___x_4360_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4359_);
lean_dec(v_stx_4239_);
v___x_4361_ = l_Lean_Syntax_isNone(v___x_4360_);
if (v___x_4361_ == 0)
{
uint8_t v___x_4362_; 
lean_inc(v___x_4360_);
v___x_4362_ = l_Lean_Syntax_matchesNull(v___x_4360_, v___x_4357_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4363_; 
lean_dec(v___x_4360_);
lean_dec(v_rhs_4358_);
lean_dec(v_patType_x3f_4349_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_letOrReassign_4238_);
v___x_4363_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4363_;
}
else
{
lean_object* v___x_4364_; lean_object* v_otherwise_x3f_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4365_ = l_Lean_Syntax_getArg(v___x_4360_, v___x_4347_);
v___x_4366_ = l_Lean_Syntax_getArg(v___x_4360_, v___x_4364_);
lean_dec(v___x_4360_);
v___x_4367_ = l_Lean_Syntax_getOptional_x3f(v___x_4366_);
lean_dec(v___x_4366_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_box(0);
v___y_4292_ = v___y_4356_;
v___y_4293_ = v___y_4352_;
v___y_4294_ = v___y_4353_;
v___y_4295_ = v___y_4354_;
v___y_4296_ = v___y_4351_;
v___y_4297_ = v___y_4350_;
v___y_4298_ = v___y_4355_;
v___y_4299_ = v_rhs_4358_;
v___y_4300_ = v_otherwise_x3f_4365_;
v___y_4301_ = v_patType_x3f_4349_;
v___y_4302_ = v___x_4368_;
goto v___jp_4291_;
}
else
{
lean_object* v_val_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
v_val_4369_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4367_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_val_4369_);
lean_dec(v___x_4367_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_val_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
v___y_4292_ = v___y_4356_;
v___y_4293_ = v___y_4352_;
v___y_4294_ = v___y_4353_;
v___y_4295_ = v___y_4354_;
v___y_4296_ = v___y_4351_;
v___y_4297_ = v___y_4350_;
v___y_4298_ = v___y_4355_;
v___y_4299_ = v_rhs_4358_;
v___y_4300_ = v_otherwise_x3f_4365_;
v___y_4301_ = v_patType_x3f_4349_;
v___y_4302_ = v___x_4374_;
goto v___jp_4291_;
}
}
}
}
}
else
{
lean_object* v___x_4377_; 
lean_dec(v___x_4360_);
v___x_4377_ = lean_box(0);
v___y_4263_ = v_patType_x3f_4349_;
v___y_4264_ = v___y_4351_;
v___y_4265_ = v___y_4353_;
v___y_4266_ = v___y_4350_;
v___y_4267_ = v_rhs_4358_;
v___y_4268_ = v___y_4352_;
v___y_4269_ = v___y_4355_;
v___y_4270_ = v___x_4377_;
v___y_4271_ = v___y_4354_;
v___y_4272_ = v___y_4356_;
v___y_4273_ = v___x_4377_;
goto v___jp_4262_;
}
}
}
else
{
lean_object* v_pattern_4389_; lean_object* v___x_4390_; lean_object* v_patType_x3f_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v_pattern_4389_ = l_Lean_Syntax_getArg(v___x_4259_, v___x_4258_);
v___x_4390_ = lean_unsigned_to_nat(1u);
v___x_4447_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4390_);
v___x_4448_ = l_Lean_Syntax_isNone(v___x_4447_);
if (v___x_4448_ == 0)
{
uint8_t v___x_4449_; 
lean_inc(v___x_4447_);
v___x_4449_ = l_Lean_Syntax_matchesNull(v___x_4447_, v___x_4390_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; 
lean_dec(v___x_4447_);
lean_dec(v_pattern_4389_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4450_;
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4451_ = l_Lean_Syntax_getArg(v___x_4447_, v___x_4258_);
lean_dec(v___x_4447_);
v___x_4452_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4451_);
v___x_4453_ = l_Lean_Syntax_isOfKind(v___x_4451_, v___x_4452_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; 
lean_dec(v___x_4451_);
lean_dec(v_pattern_4389_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4454_;
}
else
{
lean_object* v_patType_x3f_4455_; lean_object* v___x_4456_; 
v_patType_x3f_4455_ = l_Lean_Syntax_getArg(v___x_4451_, v___x_4390_);
lean_dec(v___x_4451_);
v___x_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4456_, 0, v_patType_x3f_4455_);
v_patType_x3f_4392_ = v___x_4456_;
v___y_4393_ = v_a_4242_;
v___y_4394_ = v_a_4243_;
v___y_4395_ = v_a_4244_;
v___y_4396_ = v_a_4245_;
v___y_4397_ = v_a_4246_;
v___y_4398_ = v_a_4247_;
v___y_4399_ = v_a_4248_;
goto v___jp_4391_;
}
}
}
else
{
lean_object* v___x_4457_; 
lean_dec(v___x_4447_);
v___x_4457_ = lean_box(0);
v_patType_x3f_4392_ = v___x_4457_;
v___y_4393_ = v_a_4242_;
v___y_4394_ = v_a_4243_;
v___y_4395_ = v_a_4244_;
v___y_4396_ = v_a_4245_;
v___y_4397_ = v_a_4246_;
v___y_4398_ = v_a_4247_;
v___y_4399_ = v_a_4248_;
goto v___jp_4391_;
}
v___jp_4391_:
{
lean_object* v___x_4400_; lean_object* v_rhs_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v___x_4400_ = lean_unsigned_to_nat(3u);
v_rhs_4401_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4400_);
v___x_4402_ = lean_unsigned_to_nat(4u);
v___x_4403_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4402_);
lean_dec(v_stx_4239_);
lean_inc(v___x_4403_);
v___x_4404_ = l_Lean_Syntax_matchesNull(v___x_4403_, v___x_4258_);
if (v___x_4404_ == 0)
{
uint8_t v___x_4405_; 
lean_dec(v_pattern_4389_);
v___x_4405_ = l_Lean_Syntax_isNone(v___x_4403_);
if (v___x_4405_ == 0)
{
uint8_t v___x_4406_; 
lean_inc(v___x_4403_);
v___x_4406_ = l_Lean_Syntax_matchesNull(v___x_4403_, v___x_4400_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; 
lean_dec(v___x_4403_);
lean_dec(v_rhs_4401_);
lean_dec(v_patType_x3f_4392_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_letOrReassign_4238_);
v___x_4407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4407_;
}
else
{
lean_object* v___x_4408_; lean_object* v_otherwise_x3f_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4408_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4409_ = l_Lean_Syntax_getArg(v___x_4403_, v___x_4390_);
v___x_4410_ = l_Lean_Syntax_getArg(v___x_4403_, v___x_4408_);
lean_dec(v___x_4403_);
v___x_4411_ = l_Lean_Syntax_getOptional_x3f(v___x_4410_);
lean_dec(v___x_4410_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_box(0);
v___y_4335_ = v___y_4398_;
v___y_4336_ = v___y_4394_;
v___y_4337_ = v_patType_x3f_4392_;
v___y_4338_ = v___y_4396_;
v___y_4339_ = v_otherwise_x3f_4409_;
v___y_4340_ = v___y_4399_;
v___y_4341_ = v___y_4395_;
v___y_4342_ = v___y_4397_;
v___y_4343_ = v___y_4393_;
v___y_4344_ = v_rhs_4401_;
v___y_4345_ = v___x_4412_;
goto v___jp_4334_;
}
else
{
lean_object* v_val_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
v_val_4413_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4411_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_val_4413_);
lean_dec(v___x_4411_);
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
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_val_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
v___y_4335_ = v___y_4398_;
v___y_4336_ = v___y_4394_;
v___y_4337_ = v_patType_x3f_4392_;
v___y_4338_ = v___y_4396_;
v___y_4339_ = v_otherwise_x3f_4409_;
v___y_4340_ = v___y_4399_;
v___y_4341_ = v___y_4395_;
v___y_4342_ = v___y_4397_;
v___y_4343_ = v___y_4393_;
v___y_4344_ = v_rhs_4401_;
v___y_4345_ = v___x_4418_;
goto v___jp_4334_;
}
}
}
}
}
else
{
lean_object* v___x_4421_; 
lean_dec(v___x_4403_);
v___x_4421_ = lean_box(0);
v___y_4305_ = v___y_4395_;
v___y_4306_ = v___y_4394_;
v___y_4307_ = v___y_4399_;
v___y_4308_ = v___y_4398_;
v___y_4309_ = v___y_4397_;
v___y_4310_ = v___y_4396_;
v___y_4311_ = v___y_4393_;
v___y_4312_ = v___x_4421_;
v___y_4313_ = v_rhs_4401_;
v___y_4314_ = v_patType_x3f_4392_;
v___y_4315_ = v___x_4421_;
goto v___jp_4304_;
}
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec(v___x_4403_);
lean_dec(v___x_4259_);
lean_dec(v_letOrReassign_4238_);
v___x_4422_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4423_ = l_Lean_Core_mkFreshUserName(v___x_4422_, v___y_4398_, v___y_4399_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4425_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v___x_4425_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4241_, v_tk_4240_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; uint8_t v_kind_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
v_kind_4427_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3);
v___x_4428_ = l_Lean_mkIdentFrom(v_pattern_4389_, v_a_4424_, v___x_4254_);
lean_dec(v_pattern_4389_);
v___x_4429_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4429_, 0, v_a_4426_);
v___x_4430_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4428_, v_patType_x3f_4392_, v_rhs_4401_, v___x_4429_, v_kind_4427_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
return v___x_4430_;
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_a_4424_);
lean_dec(v_rhs_4401_);
lean_dec(v_patType_x3f_4392_);
lean_dec(v_pattern_4389_);
v_a_4431_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4425_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4425_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_rhs_4401_);
lean_dec(v_patType_x3f_4392_);
lean_dec(v_pattern_4389_);
lean_dec_ref(v_dec_4241_);
v_a_4439_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4423_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4423_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
}
}
v___jp_4262_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4275_ = l_Lean_Core_mkFreshUserName(v___x_4274_, v___y_4269_, v___y_4272_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___y_4280_; uint8_t v___x_4281_; lean_object* v___x_4282_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
v___x_4277_ = l_Lean_mkIdentFrom(v___x_4259_, v_a_4276_, v___x_4261_);
v___x_4278_ = lean_box(v___x_4261_);
v___x_4279_ = lean_box(v___x_4256_);
lean_inc(v___x_4277_);
v___y_4280_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4280_, 0, v_letOrReassign_4238_);
lean_closure_set(v___y_4280_, 1, v___y_4270_);
lean_closure_set(v___y_4280_, 2, v___x_4278_);
lean_closure_set(v___y_4280_, 3, v___x_4250_);
lean_closure_set(v___y_4280_, 4, v___x_4251_);
lean_closure_set(v___y_4280_, 5, v___x_4252_);
lean_closure_set(v___y_4280_, 6, v___x_4259_);
lean_closure_set(v___y_4280_, 7, v___x_4277_);
lean_closure_set(v___y_4280_, 8, v_dec_4241_);
lean_closure_set(v___y_4280_, 9, v___x_4279_);
lean_closure_set(v___y_4280_, 10, v___y_4273_);
lean_closure_set(v___y_4280_, 11, v___x_4258_);
v___x_4281_ = 0;
v___x_4282_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4277_, v___y_4263_, v___y_4267_, v___y_4280_, v___x_4281_, v___y_4266_, v___y_4264_, v___y_4268_, v___y_4265_, v___y_4271_, v___y_4269_, v___y_4272_);
return v___x_4282_;
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v___y_4273_);
lean_dec(v___y_4270_);
lean_dec(v___y_4267_);
lean_dec(v___y_4263_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_letOrReassign_4238_);
v_a_4283_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4275_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4275_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
v___jp_4291_:
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___y_4300_);
v___y_4263_ = v___y_4301_;
v___y_4264_ = v___y_4296_;
v___y_4265_ = v___y_4294_;
v___y_4266_ = v___y_4297_;
v___y_4267_ = v___y_4299_;
v___y_4268_ = v___y_4293_;
v___y_4269_ = v___y_4298_;
v___y_4270_ = v___x_4303_;
v___y_4271_ = v___y_4295_;
v___y_4272_ = v___y_4292_;
v___y_4273_ = v___y_4302_;
goto v___jp_4262_;
}
v___jp_4304_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4317_ = l_Lean_Core_mkFreshUserName(v___x_4316_, v___y_4308_, v___y_4307_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___y_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = l_Lean_mkIdentFrom(v___x_4259_, v_a_4318_, v___x_4254_);
v___x_4320_ = lean_box(v___x_4254_);
v___x_4321_ = lean_box(v___x_4256_);
v___x_4322_ = lean_box(v___x_4261_);
lean_inc(v___x_4319_);
v___y_4323_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4323_, 0, v_letOrReassign_4238_);
lean_closure_set(v___y_4323_, 1, v___y_4312_);
lean_closure_set(v___y_4323_, 2, v___x_4320_);
lean_closure_set(v___y_4323_, 3, v___x_4250_);
lean_closure_set(v___y_4323_, 4, v___x_4251_);
lean_closure_set(v___y_4323_, 5, v___x_4252_);
lean_closure_set(v___y_4323_, 6, v___x_4259_);
lean_closure_set(v___y_4323_, 7, v___x_4319_);
lean_closure_set(v___y_4323_, 8, v_dec_4241_);
lean_closure_set(v___y_4323_, 9, v___x_4321_);
lean_closure_set(v___y_4323_, 10, v___y_4315_);
lean_closure_set(v___y_4323_, 11, v___x_4258_);
lean_closure_set(v___y_4323_, 12, v___x_4322_);
v___x_4324_ = 0;
v___x_4325_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4319_, v___y_4314_, v___y_4313_, v___y_4323_, v___x_4324_, v___y_4311_, v___y_4306_, v___y_4305_, v___y_4310_, v___y_4309_, v___y_4308_, v___y_4307_);
return v___x_4325_;
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec(v___x_4259_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_letOrReassign_4238_);
v_a_4326_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4317_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4317_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
v___jp_4334_:
{
lean_object* v___x_4346_; 
v___x_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4346_, 0, v___y_4339_);
v___y_4305_ = v___y_4341_;
v___y_4306_ = v___y_4336_;
v___y_4307_ = v___y_4340_;
v___y_4308_ = v___y_4335_;
v___y_4309_ = v___y_4342_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4343_;
v___y_4312_ = v___x_4346_;
v___y_4313_ = v___y_4344_;
v___y_4314_ = v___y_4337_;
v___y_4315_ = v___y_4345_;
goto v___jp_4304_;
}
}
}
else
{
lean_object* v___x_4458_; lean_object* v_x_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v_xType_x3f_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v_xType_x3f_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4458_ = lean_unsigned_to_nat(0u);
v_x_4459_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4458_);
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4459_);
v___x_4533_ = l_Lean_Syntax_isOfKind(v_x_4459_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_dec(v_x_4459_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4534_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4535_ = lean_unsigned_to_nat(1u);
v___x_4536_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4535_);
v___x_4537_ = l_Lean_Syntax_isNone(v___x_4536_);
if (v___x_4537_ == 0)
{
uint8_t v___x_4538_; 
lean_inc(v___x_4536_);
v___x_4538_ = l_Lean_Syntax_matchesNull(v___x_4536_, v___x_4535_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; 
lean_dec(v___x_4536_);
lean_dec(v_x_4459_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4539_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4539_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = l_Lean_Syntax_getArg(v___x_4536_, v___x_4458_);
lean_dec(v___x_4536_);
v___x_4541_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4540_);
v___x_4542_ = l_Lean_Syntax_isOfKind(v___x_4540_, v___x_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
lean_dec(v___x_4540_);
lean_dec(v_x_4459_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v___x_4543_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4543_;
}
else
{
lean_object* v_xType_x3f_4544_; lean_object* v___x_4545_; 
v_xType_x3f_4544_ = l_Lean_Syntax_getArg(v___x_4540_, v___x_4535_);
lean_dec(v___x_4540_);
v___x_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_xType_x3f_4544_);
v_xType_x3f_4477_ = v___x_4545_;
v___y_4478_ = v_a_4242_;
v___y_4479_ = v_a_4243_;
v___y_4480_ = v_a_4244_;
v___y_4481_ = v_a_4245_;
v___y_4482_ = v_a_4246_;
v___y_4483_ = v_a_4247_;
v___y_4484_ = v_a_4248_;
goto v___jp_4476_;
}
}
}
else
{
lean_object* v___x_4546_; 
lean_dec(v___x_4536_);
v___x_4546_ = lean_box(0);
v_xType_x3f_4477_ = v___x_4546_;
v___y_4478_ = v_a_4242_;
v___y_4479_ = v_a_4243_;
v___y_4480_ = v_a_4244_;
v___y_4481_ = v_a_4245_;
v___y_4482_ = v_a_4246_;
v___y_4483_ = v_a_4247_;
v___y_4484_ = v_a_4248_;
goto v___jp_4476_;
}
}
v___jp_4460_:
{
uint8_t v_kind_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_kind_4471_ = lean_ctor_get_uint8(v___y_4461_, sizeof(void*)*3);
v___x_4472_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4238_);
lean_dec(v_letOrReassign_4238_);
v___x_4473_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4473_, 0, v___y_4461_);
lean_inc(v_x_4459_);
v___x_4474_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4474_, 0, lean_box(0));
lean_closure_set(v___x_4474_, 1, v___x_4472_);
lean_closure_set(v___x_4474_, 2, v_x_4459_);
lean_closure_set(v___x_4474_, 3, v___x_4473_);
v___x_4475_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4459_, v_xType_x3f_4463_, v___y_4462_, v___x_4474_, v_kind_4471_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
return v___x_4475_;
}
v___jp_4476_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4485_ = lean_unsigned_to_nat(1u);
v___x_4486_ = lean_mk_empty_array_with_capacity(v___x_4485_);
lean_inc(v_x_4459_);
v___x_4487_ = lean_array_push(v___x_4486_, v_x_4459_);
v___x_4488_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4238_, v___x_4487_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec_ref(v___x_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref_known(v___x_4488_, 1);
v___x_4489_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4241_, v_tk_4240_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; lean_object* v_rhs_4492_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = lean_unsigned_to_nat(3u);
v_rhs_4492_ = l_Lean_Syntax_getArg(v_stx_4239_, v___x_4491_);
lean_dec(v_stx_4239_);
if (lean_obj_tag(v_letOrReassign_4238_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4477_) == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = l_Lean_TSyntax_getId(v_x_4459_);
v___x_4494_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4493_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
v___x_4496_ = l_Lean_LocalDecl_type(v_a_4495_);
lean_dec(v_a_4495_);
v___x_4497_ = l_Lean_Elab_Term_exprToSyntax(v___x_4496_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4499_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v_a_4498_);
v___y_4461_ = v_a_4490_;
v___y_4462_ = v_rhs_4492_;
v_xType_x3f_4463_ = v___x_4499_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
v___y_4469_ = v___y_4483_;
v___y_4470_ = v___y_4484_;
goto v___jp_4460_;
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_rhs_4492_);
lean_dec(v_a_4490_);
lean_dec(v_x_4459_);
v_a_4500_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4497_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4497_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_rhs_4492_);
lean_dec(v_a_4490_);
lean_dec(v_x_4459_);
v_a_4508_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4494_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4494_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
else
{
v___y_4461_ = v_a_4490_;
v___y_4462_ = v_rhs_4492_;
v_xType_x3f_4463_ = v_xType_x3f_4477_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
v___y_4469_ = v___y_4483_;
v___y_4470_ = v___y_4484_;
goto v___jp_4460_;
}
}
else
{
v___y_4461_ = v_a_4490_;
v___y_4462_ = v_rhs_4492_;
v_xType_x3f_4463_ = v_xType_x3f_4477_;
v___y_4464_ = v___y_4478_;
v___y_4465_ = v___y_4479_;
v___y_4466_ = v___y_4480_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___y_4482_;
v___y_4469_ = v___y_4483_;
v___y_4470_ = v___y_4484_;
goto v___jp_4460_;
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_xType_x3f_4477_);
lean_dec(v_x_4459_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v_a_4516_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4489_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4489_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec(v_xType_x3f_4477_);
lean_dec(v_x_4459_);
lean_dec_ref(v_dec_4241_);
lean_dec(v_stx_4239_);
lean_dec(v_letOrReassign_4238_);
v_a_4524_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4488_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4488_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4547_, lean_object* v_stx_4548_, lean_object* v_tk_4549_, lean_object* v_dec_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4547_, v_stx_4548_, v_tk_4549_, v_dec_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_tk_4549_);
return v_res_4559_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4562_ = l_Lean_stringToMessageData(v___x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4563_, lean_object* v_mutTk_x3f_4564_, lean_object* v_initConfig_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4564_) == 0)
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4563_, v_initConfig_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4573_;
}
else
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; uint8_t v___x_4579_; 
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = l_Lean_Syntax_getArg(v_letConfigStx_4563_, v___x_4574_);
v___x_4576_ = l_Lean_Syntax_getArgs(v___x_4575_);
lean_dec(v___x_4575_);
v___x_4577_ = lean_array_get_size(v___x_4576_);
lean_dec_ref(v___x_4576_);
v___x_4578_ = lean_nat_dec_eq(v___x_4577_, v___x_4574_);
v___x_4579_ = lean_bool_not(v___x_4578_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4563_, v_initConfig_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec_ref(v_initConfig_4565_);
v___x_4581_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4582_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4563_, v___x_4581_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_letConfigStx_4563_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4591_, lean_object* v_mutTk_x3f_4592_, lean_object* v_initConfig_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4591_, v_mutTk_x3f_4592_, v_initConfig_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_mutTk_x3f_4592_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4602_, lean_object* v_mutTk_x3f_4603_, lean_object* v_initConfig_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4602_, v_mutTk_x3f_4603_, v_initConfig_4604_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4614_, lean_object* v_mutTk_x3f_4615_, lean_object* v_initConfig_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4614_, v_mutTk_x3f_4615_, v_initConfig_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_mutTk_x3f_4615_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4639_, lean_object* v_dec_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4639_);
v___x_4650_ = l_Lean_Syntax_isOfKind(v_stx_4639_, v___x_4649_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; 
lean_dec_ref(v_dec_4640_);
lean_dec(v_stx_4639_);
v___x_4651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4651_;
}
else
{
lean_object* v___x_4652_; lean_object* v_tk_4653_; lean_object* v_mutTk_x3f_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v___x_4652_ = lean_unsigned_to_nat(0u);
v_tk_4653_ = l_Lean_Syntax_getArg(v_stx_4639_, v___x_4652_);
v___x_4686_ = lean_unsigned_to_nat(1u);
v___x_4687_ = l_Lean_Syntax_getArg(v_stx_4639_, v___x_4686_);
v___x_4688_ = l_Lean_Syntax_isNone(v___x_4687_);
if (v___x_4688_ == 0)
{
uint8_t v___x_4689_; 
lean_inc(v___x_4687_);
v___x_4689_ = l_Lean_Syntax_matchesNull(v___x_4687_, v___x_4686_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; 
lean_dec(v___x_4687_);
lean_dec(v_tk_4653_);
lean_dec_ref(v_dec_4640_);
lean_dec(v_stx_4639_);
v___x_4690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4690_;
}
else
{
lean_object* v_mutTk_x3f_4691_; lean_object* v___x_4692_; 
v_mutTk_x3f_4691_ = l_Lean_Syntax_getArg(v___x_4687_, v___x_4652_);
lean_dec(v___x_4687_);
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v_mutTk_x3f_4691_);
v_mutTk_x3f_4655_ = v___x_4692_;
v___y_4656_ = v_a_4641_;
v___y_4657_ = v_a_4642_;
v___y_4658_ = v_a_4643_;
v___y_4659_ = v_a_4644_;
v___y_4660_ = v_a_4645_;
v___y_4661_ = v_a_4646_;
v___y_4662_ = v_a_4647_;
goto v___jp_4654_;
}
}
else
{
lean_object* v___x_4693_; 
lean_dec(v___x_4687_);
v___x_4693_ = lean_box(0);
v_mutTk_x3f_4655_ = v___x_4693_;
v___y_4656_ = v_a_4641_;
v___y_4657_ = v_a_4642_;
v___y_4658_ = v_a_4643_;
v___y_4659_ = v_a_4644_;
v___y_4660_ = v_a_4645_;
v___y_4661_ = v_a_4646_;
v___y_4662_ = v_a_4647_;
goto v___jp_4654_;
}
v___jp_4654_:
{
lean_object* v___x_4663_; lean_object* v_config_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4663_ = lean_unsigned_to_nat(2u);
v_config_4664_ = l_Lean_Syntax_getArg(v_stx_4639_, v___x_4663_);
v___x_4665_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4664_);
v___x_4666_ = l_Lean_Syntax_isOfKind(v_config_4664_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; 
lean_dec(v_config_4664_);
lean_dec(v_mutTk_x3f_4655_);
lean_dec(v_tk_4653_);
lean_dec_ref(v_dec_4640_);
lean_dec(v_stx_4639_);
v___x_4667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4667_;
}
else
{
lean_object* v___x_4668_; lean_object* v_decl_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4668_ = lean_unsigned_to_nat(3u);
v_decl_4669_ = l_Lean_Syntax_getArg(v_stx_4639_, v___x_4668_);
lean_dec(v_stx_4639_);
v___x_4670_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4669_);
v___x_4671_ = l_Lean_Syntax_isOfKind(v_decl_4669_, v___x_4670_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_dec(v_decl_4669_);
lean_dec(v_config_4664_);
lean_dec(v_mutTk_x3f_4655_);
lean_dec(v_tk_4653_);
lean_dec_ref(v_dec_4640_);
v___x_4672_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4672_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4674_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4664_, v_mutTk_x3f_4655_, v___x_4673_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_mutTk_x3f_4655_);
v___x_4677_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4675_, v___x_4676_, v_decl_4669_, v_tk_4653_, v_dec_4640_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
return v___x_4677_;
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v_decl_4669_);
lean_dec(v_mutTk_x3f_4655_);
lean_dec(v_tk_4653_);
lean_dec_ref(v_dec_4640_);
v_a_4678_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4674_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4674_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4694_, lean_object* v_dec_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_Elab_Do_elabDoLet(v_stx_4694_, v_dec_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4712_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4713_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4714_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4715_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4716_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4712_, v___x_4713_, v___x_4714_, v___x_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4724_, lean_object* v_dec_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4734_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4724_);
v___x_4735_ = l_Lean_Syntax_isOfKind(v_stx_4724_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec_ref(v_dec_4725_);
lean_dec(v_stx_4724_);
v___x_4736_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4736_;
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = l_Lean_Syntax_getArg(v_stx_4724_, v___x_4737_);
v___x_4739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4738_);
v___x_4740_ = l_Lean_Syntax_isOfKind(v___x_4738_, v___x_4739_);
if (v___x_4740_ == 0)
{
lean_object* v___x_4741_; 
lean_dec(v___x_4738_);
lean_dec_ref(v_dec_4725_);
lean_dec(v_stx_4724_);
v___x_4741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4741_;
}
else
{
lean_object* v___x_4742_; lean_object* v_decl_4743_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v___x_4742_ = lean_unsigned_to_nat(2u);
v_decl_4743_ = l_Lean_Syntax_getArg(v_stx_4724_, v___x_4742_);
v___x_4744_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4743_);
v___x_4745_ = l_Lean_Syntax_isOfKind(v_decl_4743_, v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_dec(v_decl_4743_);
lean_dec(v___x_4738_);
lean_dec_ref(v_dec_4725_);
lean_dec(v_stx_4724_);
v___x_4746_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4746_;
}
else
{
uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4747_ = 0;
v___x_4748_ = lean_box(0);
v___x_4749_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1, v___x_4745_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1 + 1, v___x_4747_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1 + 2, v___x_4747_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1 + 3, v___x_4747_);
lean_ctor_set_uint8(v___x_4749_, sizeof(void*)*1 + 4, v___x_4747_);
v___x_4750_ = l_Lean_Elab_Term_mkLetConfig(v___x_4738_, v___x_4749_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v___x_4752_; lean_object* v_tk_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
lean_inc(v_a_4751_);
lean_dec_ref_known(v___x_4750_, 1);
v___x_4752_ = lean_unsigned_to_nat(0u);
v_tk_4753_ = l_Lean_Syntax_getArg(v_stx_4724_, v___x_4752_);
lean_dec(v_stx_4724_);
v___x_4754_ = lean_box(1);
v___x_4755_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4751_, v___x_4754_, v_decl_4743_, v_tk_4753_, v_dec_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
return v___x_4755_;
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_decl_4743_);
lean_dec_ref(v_dec_4725_);
lean_dec(v_stx_4724_);
v_a_4756_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4750_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4750_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4764_, lean_object* v_dec_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_Elab_Do_elabDoHave(v_stx_4764_, v_dec_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4782_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4783_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4784_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4785_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4786_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4782_, v___x_4783_, v___x_4784_, v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4791_, lean_object* v___x_4792_, lean_object* v___x_4793_, lean_object* v___x_4794_, lean_object* v_decls_4795_, lean_object* v_a_4796_, uint8_t v___x_4797_, lean_object* v_body_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v_ref_4807_; uint8_t v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_ref_4807_ = lean_ctor_get(v___y_4804_, 5);
v___x_4808_ = 0;
v___x_4809_ = l_Lean_SourceInfo_fromRef(v_ref_4807_, v___x_4808_);
v___x_4810_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4811_ = l_Lean_Name_mkStr4(v___x_4791_, v___x_4792_, v___x_4793_, v___x_4810_);
v___x_4812_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4809_, 4);
v___x_4813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4809_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
v___x_4814_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4809_);
lean_ctor_set(v___x_4815_, 1, v___x_4814_);
v___x_4816_ = l_Lean_Syntax_node2(v___x_4809_, v___x_4794_, v___x_4813_, v___x_4815_);
v___x_4817_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4809_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = l_Lean_Syntax_node4(v___x_4809_, v___x_4811_, v___x_4816_, v_decls_4795_, v___x_4818_, v_body_4798_);
v___x_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4820_, 0, v_a_4796_);
v___x_4821_ = l_Lean_Elab_Term_elabTerm(v___x_4819_, v___x_4820_, v___x_4797_, v___x_4797_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4822_, lean_object* v___x_4823_, lean_object* v___x_4824_, lean_object* v___x_4825_, lean_object* v_decls_4826_, lean_object* v_a_4827_, lean_object* v___x_4828_, lean_object* v_body_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
uint8_t v___x_5027__boxed_4838_; lean_object* v_res_4839_; 
v___x_5027__boxed_4838_ = lean_unbox(v___x_4828_);
v_res_4839_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4822_, v___x_4823_, v___x_4824_, v___x_4825_, v_decls_4826_, v_a_4827_, v___x_5027__boxed_4838_, v_body_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec_ref(v___y_4830_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
if (lean_obj_tag(v_a_4840_) == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = l_List_reverse___redArg(v_a_4841_);
return v___x_4842_;
}
else
{
lean_object* v_head_4843_; lean_object* v_tail_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4853_; 
v_head_4843_ = lean_ctor_get(v_a_4840_, 0);
v_tail_4844_ = lean_ctor_get(v_a_4840_, 1);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_a_4840_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4846_ = v_a_4840_;
v_isShared_4847_ = v_isSharedCheck_4853_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_tail_4844_);
lean_inc(v_head_4843_);
lean_dec(v_a_4840_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4853_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
v___x_4848_ = l_Lean_MessageData_ofSyntax(v_head_4843_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 1, v_a_4841_);
lean_ctor_set(v___x_4846_, 0, v___x_4848_);
v___x_4850_ = v___x_4846_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4848_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v_a_4841_);
v___x_4850_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
v_a_4840_ = v_tail_4844_;
v_a_4841_ = v___x_4850_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4871_ = l_Lean_stringToMessageData(v___x_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4872_, lean_object* v_dec_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4883_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4884_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4885_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4872_);
v___x_4886_ = l_Lean_Syntax_isOfKind(v_stx_4872_, v___x_4885_);
if (v___x_4886_ == 0)
{
lean_object* v___x_4887_; 
lean_dec_ref(v_dec_4873_);
lean_dec(v_stx_4872_);
v___x_4887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4887_;
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = l_Lean_Syntax_getArg(v_stx_4872_, v___x_4888_);
v___x_4890_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4889_);
v___x_4891_ = l_Lean_Syntax_isOfKind(v___x_4889_, v___x_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; 
lean_dec(v___x_4889_);
lean_dec_ref(v_dec_4873_);
lean_dec(v_stx_4872_);
v___x_4892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4892_;
}
else
{
lean_object* v___x_4893_; lean_object* v_decls_4894_; lean_object* v___x_4895_; uint8_t v___x_4896_; 
v___x_4893_ = lean_unsigned_to_nat(1u);
v_decls_4894_ = l_Lean_Syntax_getArg(v_stx_4872_, v___x_4893_);
lean_dec(v_stx_4872_);
v___x_4895_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4894_);
v___x_4896_ = l_Lean_Syntax_isOfKind(v_decls_4894_, v___x_4895_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; 
lean_dec(v_decls_4894_);
lean_dec(v___x_4889_);
lean_dec_ref(v_dec_4873_);
v___x_4897_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4897_;
}
else
{
lean_object* v_tk_4898_; lean_object* v___x_4899_; 
v_tk_4898_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4888_);
lean_dec(v___x_4889_);
v___x_4899_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4873_, v_tk_4898_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
lean_dec(v_tk_4898_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4901_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref_known(v___x_4899_, 1);
lean_inc(v_decls_4894_);
v___x_4901_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4894_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v_doBlockResultType_4903_; lean_object* v___x_4904_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4902_);
lean_dec_ref_known(v___x_4901_, 1);
v_doBlockResultType_4903_ = lean_ctor_get(v_a_4874_, 3);
lean_inc_ref(v_doBlockResultType_4903_);
v___x_4904_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4903_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4906_; lean_object* v___f_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_a_4905_);
lean_dec_ref_known(v___x_4904_, 1);
v___x_4906_ = lean_box(v___x_4896_);
v___f_4907_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4907_, 0, v___x_4882_);
lean_closure_set(v___f_4907_, 1, v___x_4883_);
lean_closure_set(v___f_4907_, 2, v___x_4884_);
lean_closure_set(v___f_4907_, 3, v___x_4890_);
lean_closure_set(v___f_4907_, 4, v_decls_4894_);
lean_closure_set(v___f_4907_, 5, v_a_4905_);
lean_closure_set(v___f_4907_, 6, v___x_4906_);
v___x_4908_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4909_ = lean_array_to_list(v_a_4902_);
v___x_4910_ = lean_box(0);
v___x_4911_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4909_, v___x_4910_);
v___x_4912_ = l_Lean_MessageData_ofList(v___x_4911_);
v___x_4913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4908_);
lean_ctor_set(v___x_4913_, 1, v___x_4912_);
v___x_4914_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4914_, 0, v_a_4900_);
v___x_4915_ = lean_box(0);
v___x_4916_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4913_, v___x_4914_, v___f_4907_, v___x_4915_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
return v___x_4916_;
}
else
{
lean_dec(v_a_4902_);
lean_dec(v_a_4900_);
lean_dec(v_decls_4894_);
return v___x_4904_;
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec(v_a_4900_);
lean_dec(v_decls_4894_);
v_a_4917_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4901_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4901_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v_decls_4894_);
v_a_4925_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4899_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4899_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_4933_, lean_object* v_dec_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_4933_, v_dec_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec_ref(v_a_4935_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4951_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4952_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_4953_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_4954_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_4955_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4951_, v___x_4952_, v___x_4953_, v___x_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_4971_, lean_object* v_dec_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v___y_4982_; lean_object* v___y_4983_; uint8_t v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; lean_object* v___y_4998_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5014_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_4971_);
v___x_5015_ = l_Lean_Syntax_isOfKind(v_stx_4971_, v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; 
lean_dec_ref(v_dec_4972_);
lean_dec(v_stx_4971_);
v___x_5016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5016_;
}
else
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5017_ = lean_unsigned_to_nat(0u);
v___x_5018_ = l_Lean_Syntax_getArg(v_stx_4971_, v___x_5017_);
lean_dec(v_stx_4971_);
v___x_5019_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5018_);
v___x_5020_ = l_Lean_Syntax_isOfKind(v___x_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; uint8_t v___x_5022_; 
v___x_5021_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5018_);
v___x_5022_ = l_Lean_Syntax_isOfKind(v___x_5018_, v___x_5021_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; 
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5023_;
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v_decl_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5024_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5025_ = lean_unsigned_to_nat(1u);
v___x_5026_ = lean_mk_empty_array_with_capacity(v___x_5025_);
v___x_5027_ = lean_array_push(v___x_5026_, v___x_5018_);
v___x_5028_ = lean_box(2);
v_decl_5029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5029_, 0, v___x_5028_);
lean_ctor_set(v_decl_5029_, 1, v___x_5024_);
lean_ctor_set(v_decl_5029_, 2, v___x_5027_);
v___x_5030_ = lean_box(0);
v___x_5031_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*1, v___x_5020_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*1 + 1, v___x_5020_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*1 + 2, v___x_5020_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*1 + 3, v___x_5020_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*1 + 4, v___x_5020_);
v___x_5032_ = lean_box(2);
lean_inc_ref(v_decl_5029_);
v___x_5033_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5031_, v___x_5032_, v_decl_5029_, v_decl_5029_, v_dec_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
return v___x_5033_;
}
}
else
{
lean_object* v___x_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; 
v___x_5034_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5017_);
v___x_5035_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5034_);
v___x_5036_ = l_Lean_Syntax_isOfKind(v___x_5034_, v___x_5035_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; 
lean_dec(v___x_5034_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5037_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5037_;
}
else
{
lean_object* v___x_5038_; lean_object* v_xType_x3f_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___x_5067_; uint8_t v___x_5068_; 
v___x_5038_ = l_Lean_Syntax_getArg(v___x_5034_, v___x_5017_);
lean_dec(v___x_5034_);
v___x_5067_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5038_);
v___x_5068_ = l_Lean_Syntax_isOfKind(v___x_5038_, v___x_5067_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
lean_dec(v___x_5038_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5069_;
}
else
{
lean_object* v___x_5070_; lean_object* v___x_5071_; uint8_t v___x_5072_; 
v___x_5070_ = lean_unsigned_to_nat(1u);
v___x_5071_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5070_);
v___x_5072_ = l_Lean_Syntax_matchesNull(v___x_5071_, v___x_5017_);
if (v___x_5072_ == 0)
{
lean_object* v___x_5073_; 
lean_dec(v___x_5038_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5073_;
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; 
v___x_5074_ = lean_unsigned_to_nat(2u);
v___x_5075_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5074_);
v___x_5076_ = l_Lean_Syntax_isNone(v___x_5075_);
if (v___x_5076_ == 0)
{
uint8_t v___x_5077_; 
lean_inc(v___x_5075_);
v___x_5077_ = l_Lean_Syntax_matchesNull(v___x_5075_, v___x_5070_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; 
lean_dec(v___x_5075_);
lean_dec(v___x_5038_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5078_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5078_;
}
else
{
lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v___x_5079_ = l_Lean_Syntax_getArg(v___x_5075_, v___x_5017_);
lean_dec(v___x_5075_);
v___x_5080_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5079_);
v___x_5081_ = l_Lean_Syntax_isOfKind(v___x_5079_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; 
lean_dec(v___x_5079_);
lean_dec(v___x_5038_);
lean_dec(v___x_5018_);
lean_dec_ref(v_dec_4972_);
v___x_5082_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5082_;
}
else
{
lean_object* v_xType_x3f_5083_; lean_object* v___x_5084_; 
v_xType_x3f_5083_ = l_Lean_Syntax_getArg(v___x_5079_, v___x_5070_);
lean_dec(v___x_5079_);
v___x_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5084_, 0, v_xType_x3f_5083_);
v_xType_x3f_5040_ = v___x_5084_;
v___y_5041_ = v_a_4973_;
v___y_5042_ = v_a_4974_;
v___y_5043_ = v_a_4975_;
v___y_5044_ = v_a_4976_;
v___y_5045_ = v_a_4977_;
v___y_5046_ = v_a_4978_;
v___y_5047_ = v_a_4979_;
goto v___jp_5039_;
}
}
}
else
{
lean_object* v___x_5085_; 
lean_dec(v___x_5075_);
v___x_5085_ = lean_box(0);
v_xType_x3f_5040_ = v___x_5085_;
v___y_5041_ = v_a_4973_;
v___y_5042_ = v_a_4974_;
v___y_5043_ = v_a_4975_;
v___y_5044_ = v_a_4976_;
v___y_5045_ = v_a_4977_;
v___y_5046_ = v_a_4978_;
v___y_5047_ = v_a_4979_;
goto v___jp_5039_;
}
}
}
v___jp_5039_:
{
lean_object* v_ref_5048_; lean_object* v___x_5049_; lean_object* v_tk_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; uint8_t v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_ref_5048_ = lean_ctor_get(v___y_5046_, 5);
v___x_5049_ = lean_unsigned_to_nat(3u);
v_tk_5050_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5049_);
v___x_5051_ = lean_unsigned_to_nat(4u);
v___x_5052_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5051_);
lean_dec(v___x_5018_);
v___x_5053_ = 0;
v___x_5054_ = l_Lean_SourceInfo_fromRef(v_ref_5048_, v___x_5053_);
v___x_5055_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5054_, 2);
v___x_5056_ = l_Lean_Syntax_node1(v___x_5054_, v___x_5035_, v___x_5038_);
v___x_5057_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5058_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5054_);
lean_ctor_set(v___x_5059_, 1, v___x_5057_);
lean_ctor_set(v___x_5059_, 2, v___x_5058_);
if (lean_obj_tag(v_xType_x3f_5040_) == 1)
{
lean_object* v_val_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_val_5060_ = lean_ctor_get(v_xType_x3f_5040_, 0);
lean_inc(v_val_5060_);
lean_dec_ref_known(v_xType_x3f_5040_, 1);
v___x_5061_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5062_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5054_, 2);
v___x_5063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5054_);
lean_ctor_set(v___x_5063_, 1, v___x_5062_);
v___x_5064_ = l_Lean_Syntax_node2(v___x_5054_, v___x_5061_, v___x_5063_, v_val_5060_);
v___x_5065_ = l_Array_mkArray1___redArg(v___x_5064_);
v___y_4982_ = v___y_5045_;
v___y_4983_ = v___x_5052_;
v___y_4984_ = v___x_5053_;
v___y_4985_ = v___y_5041_;
v___y_4986_ = v___x_5055_;
v___y_4987_ = v___y_5047_;
v___y_4988_ = v___x_5054_;
v___y_4989_ = v___y_5042_;
v___y_4990_ = v___x_5057_;
v___y_4991_ = v___y_5046_;
v___y_4992_ = v___x_5059_;
v___y_4993_ = v___y_5043_;
v___y_4994_ = v___x_5058_;
v___y_4995_ = v___x_5056_;
v___y_4996_ = v___y_5044_;
v___y_4997_ = v_tk_5050_;
v___y_4998_ = v___x_5065_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5066_; 
lean_dec(v_xType_x3f_5040_);
v___x_5066_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_4982_ = v___y_5045_;
v___y_4983_ = v___x_5052_;
v___y_4984_ = v___x_5053_;
v___y_4985_ = v___y_5041_;
v___y_4986_ = v___x_5055_;
v___y_4987_ = v___y_5047_;
v___y_4988_ = v___x_5054_;
v___y_4989_ = v___y_5042_;
v___y_4990_ = v___x_5057_;
v___y_4991_ = v___y_5046_;
v___y_4992_ = v___x_5059_;
v___y_4993_ = v___y_5043_;
v___y_4994_ = v___x_5058_;
v___y_4995_ = v___x_5056_;
v___y_4996_ = v___y_5044_;
v___y_4997_ = v_tk_5050_;
v___y_4998_ = v___x_5066_;
goto v___jp_4981_;
}
}
}
}
}
v___jp_4981_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
lean_inc_ref(v___y_4994_);
v___x_4999_ = l_Array_append___redArg(v___y_4994_, v___y_4998_);
lean_dec_ref(v___y_4998_);
lean_inc(v___y_4990_);
lean_inc_n(v___y_4988_, 2);
v___x_5000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5000_, 0, v___y_4988_);
lean_ctor_set(v___x_5000_, 1, v___y_4990_);
lean_ctor_set(v___x_5000_, 2, v___x_4999_);
v___x_5001_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___y_4988_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
lean_inc(v___y_4986_);
v___x_5003_ = l_Lean_Syntax_node5(v___y_4988_, v___y_4986_, v___y_4995_, v___y_4992_, v___x_5000_, v___x_5002_, v___y_4983_);
v___x_5004_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5005_ = lean_unsigned_to_nat(1u);
v___x_5006_ = lean_mk_empty_array_with_capacity(v___x_5005_);
v___x_5007_ = lean_array_push(v___x_5006_, v___x_5003_);
v___x_5008_ = lean_box(2);
v___x_5009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5008_);
lean_ctor_set(v___x_5009_, 1, v___x_5004_);
lean_ctor_set(v___x_5009_, 2, v___x_5007_);
v___x_5010_ = lean_box(0);
v___x_5011_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*1, v___y_4984_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*1 + 1, v___y_4984_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*1 + 2, v___y_4984_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*1 + 3, v___y_4984_);
lean_ctor_set_uint8(v___x_5011_, sizeof(void*)*1 + 4, v___y_4984_);
v___x_5012_ = lean_box(2);
v___x_5013_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5011_, v___x_5012_, v___x_5009_, v___y_4997_, v_dec_4972_, v___y_4985_, v___y_4989_, v___y_4993_, v___y_4996_, v___y_4982_, v___y_4991_, v___y_4987_);
return v___x_5013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5086_, lean_object* v_dec_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5086_, v_dec_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
lean_dec(v_a_5094_);
lean_dec_ref(v_a_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_a_5091_);
lean_dec(v_a_5090_);
lean_dec_ref(v_a_5089_);
lean_dec_ref(v_a_5088_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5104_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5105_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5106_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5107_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5108_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5104_, v___x_5105_, v___x_5106_, v___x_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
uint8_t v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5120_ = 0;
v___x_5121_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5111_, v___x_5120_);
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v_____do__lift_5123_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5152_, size_t v_sz_5153_, size_t v_i_5154_, lean_object* v_b_5155_, lean_object* v___y_5156_){
_start:
{
uint8_t v___x_5158_; 
v___x_5158_ = lean_usize_dec_lt(v_i_5154_, v_sz_5153_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v_b_5155_);
return v___x_5159_;
}
else
{
lean_object* v_ref_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v_a_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; size_t v___x_5197_; size_t v___x_5198_; 
v_ref_5160_ = lean_ctor_get(v___y_5156_, 5);
v___x_5161_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5163_ = lean_array_uget_borrowed(v_as_5152_, v_i_5154_);
v___x_5164_ = 0;
v___x_5165_ = l_Lean_SourceInfo_fromRef(v_ref_5160_, v___x_5164_);
v___x_5166_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5168_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5169_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5165_, 17);
v___x_5170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5170_, 0, v___x_5165_);
lean_ctor_set(v___x_5170_, 1, v___x_5169_);
v___x_5171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5165_);
lean_ctor_set(v___x_5172_, 1, v___x_5171_);
v___x_5173_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5166_, v___x_5172_);
v___x_5174_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5165_);
lean_ctor_set(v___x_5175_, 1, v___x_5166_);
lean_ctor_set(v___x_5175_, 2, v___x_5174_);
lean_inc_ref_n(v___x_5175_, 3);
v___x_5176_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5161_, v___x_5175_);
v___x_5177_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5178_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5179_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5163_, 2);
v___x_5180_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5179_, v_a_5163_);
v___x_5181_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5165_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
v___x_5183_ = l_Lean_Syntax_node5(v___x_5165_, v___x_5178_, v___x_5180_, v___x_5175_, v___x_5175_, v___x_5182_, v_a_5163_);
v___x_5184_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5177_, v___x_5183_);
v___x_5185_ = l_Lean_Syntax_node4(v___x_5165_, v___x_5168_, v___x_5170_, v___x_5173_, v___x_5176_, v___x_5184_);
v___x_5186_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5165_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5166_, v___x_5187_);
v___x_5189_ = l_Lean_Syntax_node2(v___x_5165_, v___x_5167_, v___x_5185_, v___x_5188_);
v___x_5190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5165_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l_Lean_Syntax_node2(v___x_5165_, v___x_5190_, v___x_5192_, v_b_5155_);
v___x_5194_ = l_Lean_Syntax_node2(v___x_5165_, v___x_5167_, v___x_5193_, v___x_5175_);
v___x_5195_ = l_Lean_Syntax_node2(v___x_5165_, v___x_5166_, v___x_5189_, v___x_5194_);
v___x_5196_ = l_Lean_Syntax_node1(v___x_5165_, v___x_5162_, v___x_5195_);
v___x_5197_ = ((size_t)1ULL);
v___x_5198_ = lean_usize_add(v_i_5154_, v___x_5197_);
v_i_5154_ = v___x_5198_;
v_b_5155_ = v___x_5196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5200_, lean_object* v_sz_5201_, lean_object* v_i_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
size_t v_sz_boxed_5206_; size_t v_i_boxed_5207_; lean_object* v_res_5208_; 
v_sz_boxed_5206_ = lean_unbox_usize(v_sz_5201_);
lean_dec(v_sz_5201_);
v_i_boxed_5207_ = lean_unbox_usize(v_i_5202_);
lean_dec(v_i_5202_);
v_res_5208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5200_, v_sz_boxed_5206_, v_i_boxed_5207_, v_b_5203_, v___y_5204_);
lean_dec_ref(v___y_5204_);
lean_dec_ref(v_as_5200_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5209_, size_t v_sz_5210_, size_t v_i_5211_, lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
uint8_t v___x_5221_; 
v___x_5221_ = lean_usize_dec_lt(v_i_5211_, v_sz_5210_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; 
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v_b_5212_);
return v___x_5222_;
}
else
{
lean_object* v_ref_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v_a_5226_; uint8_t v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; size_t v___x_5260_; size_t v___x_5261_; lean_object* v___x_5262_; 
v_ref_5223_ = lean_ctor_get(v___y_5218_, 5);
v___x_5224_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5226_ = lean_array_uget_borrowed(v_as_5209_, v_i_5211_);
v___x_5227_ = 0;
v___x_5228_ = l_Lean_SourceInfo_fromRef(v_ref_5223_, v___x_5227_);
v___x_5229_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5231_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5232_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5228_, 17);
v___x_5233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5228_);
lean_ctor_set(v___x_5233_, 1, v___x_5232_);
v___x_5234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5228_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5229_, v___x_5235_);
v___x_5237_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5228_);
lean_ctor_set(v___x_5238_, 1, v___x_5229_);
lean_ctor_set(v___x_5238_, 2, v___x_5237_);
lean_inc_ref_n(v___x_5238_, 3);
v___x_5239_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5224_, v___x_5238_);
v___x_5240_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5242_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5226_, 2);
v___x_5243_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5242_, v_a_5226_);
v___x_5244_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5228_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = l_Lean_Syntax_node5(v___x_5228_, v___x_5241_, v___x_5243_, v___x_5238_, v___x_5238_, v___x_5245_, v_a_5226_);
v___x_5247_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5240_, v___x_5246_);
v___x_5248_ = l_Lean_Syntax_node4(v___x_5228_, v___x_5231_, v___x_5233_, v___x_5236_, v___x_5239_, v___x_5247_);
v___x_5249_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5228_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
v___x_5251_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5229_, v___x_5250_);
v___x_5252_ = l_Lean_Syntax_node2(v___x_5228_, v___x_5230_, v___x_5248_, v___x_5251_);
v___x_5253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5228_);
lean_ctor_set(v___x_5255_, 1, v___x_5254_);
v___x_5256_ = l_Lean_Syntax_node2(v___x_5228_, v___x_5253_, v___x_5255_, v_b_5212_);
v___x_5257_ = l_Lean_Syntax_node2(v___x_5228_, v___x_5230_, v___x_5256_, v___x_5238_);
v___x_5258_ = l_Lean_Syntax_node2(v___x_5228_, v___x_5229_, v___x_5252_, v___x_5257_);
v___x_5259_ = l_Lean_Syntax_node1(v___x_5228_, v___x_5225_, v___x_5258_);
v___x_5260_ = ((size_t)1ULL);
v___x_5261_ = lean_usize_add(v_i_5211_, v___x_5260_);
v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5209_, v_sz_5210_, v___x_5261_, v___x_5259_, v___y_5218_);
return v___x_5262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5263_, lean_object* v_sz_5264_, lean_object* v_i_5265_, lean_object* v_b_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
size_t v_sz_boxed_5275_; size_t v_i_boxed_5276_; lean_object* v_res_5277_; 
v_sz_boxed_5275_ = lean_unbox_usize(v_sz_5264_);
lean_dec(v_sz_5264_);
v_i_boxed_5276_ = lean_unbox_usize(v_i_5265_);
lean_dec(v_i_5265_);
v_res_5277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5263_, v_sz_boxed_5275_, v_i_boxed_5276_, v_b_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec_ref(v_as_5263_);
return v_res_5277_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5317_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5318_ = l_String_toRawSubstring_x27(v___x_5317_);
return v___x_5318_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5333_ = l_String_toRawSubstring_x27(v___x_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5350_, lean_object* v_dec_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
lean_object* v___x_5360_; uint8_t v___x_5361_; 
v___x_5360_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5350_);
v___x_5361_ = l_Lean_Syntax_isOfKind(v_stx_5350_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; 
lean_dec_ref(v_dec_5351_);
lean_dec(v_stx_5350_);
v___x_5362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5362_;
}
else
{
uint8_t v___y_5364_; lean_object* v___y_5365_; lean_object* v___y_5366_; lean_object* v___y_5367_; lean_object* v___y_5368_; lean_object* v_body_5369_; lean_object* v___y_5370_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; uint8_t v___y_5456_; uint8_t v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; lean_object* v_a_5465_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; uint8_t v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v_mutTk_x3f_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___x_5595_; lean_object* v___x_5596_; uint8_t v___x_5597_; 
v___x_5595_ = lean_unsigned_to_nat(1u);
v___x_5596_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5595_);
v___x_5597_ = l_Lean_Syntax_isNone(v___x_5596_);
if (v___x_5597_ == 0)
{
uint8_t v___x_5598_; 
lean_inc(v___x_5596_);
v___x_5598_ = l_Lean_Syntax_matchesNull(v___x_5596_, v___x_5595_);
if (v___x_5598_ == 0)
{
lean_object* v___x_5599_; 
lean_dec(v___x_5596_);
lean_dec_ref(v_dec_5351_);
lean_dec(v_stx_5350_);
v___x_5599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5599_;
}
else
{
lean_object* v___x_5600_; lean_object* v_mutTk_x3f_5601_; lean_object* v___x_5602_; 
v___x_5600_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5601_ = l_Lean_Syntax_getArg(v___x_5596_, v___x_5600_);
lean_dec(v___x_5596_);
v___x_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5602_, 0, v_mutTk_x3f_5601_);
v_mutTk_x3f_5564_ = v___x_5602_;
v___y_5565_ = v_a_5352_;
v___y_5566_ = v_a_5353_;
v___y_5567_ = v_a_5354_;
v___y_5568_ = v_a_5355_;
v___y_5569_ = v_a_5356_;
v___y_5570_ = v_a_5357_;
v___y_5571_ = v_a_5358_;
goto v___jp_5563_;
}
}
else
{
lean_object* v___x_5603_; 
lean_dec(v___x_5596_);
v___x_5603_ = lean_box(0);
v_mutTk_x3f_5564_ = v___x_5603_;
v___y_5565_ = v_a_5352_;
v___y_5566_ = v_a_5353_;
v___y_5567_ = v_a_5354_;
v___y_5568_ = v_a_5355_;
v___y_5569_ = v_a_5356_;
v___y_5570_ = v_a_5357_;
v___y_5571_ = v_a_5358_;
goto v___jp_5563_;
}
v___jp_5363_:
{
lean_object* v_eq_x3f_5377_; 
v_eq_x3f_5377_ = lean_ctor_get(v___y_5367_, 0);
lean_inc(v_eq_x3f_5377_);
lean_dec_ref(v___y_5367_);
if (lean_obj_tag(v_eq_x3f_5377_) == 1)
{
lean_object* v_val_5378_; lean_object* v_ref_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v_val_5378_ = lean_ctor_get(v_eq_x3f_5377_, 0);
lean_inc(v_val_5378_);
lean_dec_ref_known(v_eq_x3f_5377_, 1);
v_ref_5379_ = lean_ctor_get(v___y_5375_, 5);
v___x_5380_ = l_Lean_SourceInfo_fromRef(v_ref_5379_, v___y_5364_);
v___x_5381_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5382_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5380_, 19);
v___x_5383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5380_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5385_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5380_);
lean_ctor_set(v___x_5386_, 1, v___x_5384_);
lean_ctor_set(v___x_5386_, 2, v___x_5385_);
v___x_5387_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5388_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5380_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5384_, v_val_5378_, v___x_5389_);
v___x_5391_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5387_, v___x_5390_, v___y_5366_);
v___x_5392_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5384_, v___x_5391_);
v___x_5393_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5394_, 0, v___x_5380_);
lean_ctor_set(v___x_5394_, 1, v___x_5393_);
v___x_5395_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5396_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5397_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5380_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5384_, v___y_5365_);
v___x_5400_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5384_, v___x_5399_);
v___x_5401_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5380_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
lean_inc_ref(v___x_5402_);
lean_inc_ref(v___x_5398_);
v___x_5403_ = l_Lean_Syntax_node4(v___x_5380_, v___x_5396_, v___x_5398_, v___x_5400_, v___x_5402_, v_body_5369_);
v___x_5404_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5405_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5380_);
lean_ctor_set(v___x_5406_, 1, v___x_5405_);
v___x_5407_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5404_, v___x_5406_);
v___x_5408_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5384_, v___x_5407_);
v___x_5409_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5384_, v___x_5408_);
v___x_5410_ = l_Lean_Syntax_node4(v___x_5380_, v___x_5396_, v___x_5398_, v___x_5409_, v___x_5402_, v___y_5368_);
v___x_5411_ = l_Lean_Syntax_node2(v___x_5380_, v___x_5384_, v___x_5403_, v___x_5410_);
v___x_5412_ = l_Lean_Syntax_node1(v___x_5380_, v___x_5395_, v___x_5411_);
lean_inc_ref_n(v___x_5386_, 2);
v___x_5413_ = l_Lean_Syntax_node7(v___x_5380_, v___x_5381_, v___x_5383_, v___x_5386_, v___x_5386_, v___x_5386_, v___x_5392_, v___x_5394_, v___x_5412_);
v___x_5414_ = l_Lean_Elab_Do_elabDoElem(v___x_5413_, v_dec_5351_, v___x_5361_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
return v___x_5414_;
}
else
{
lean_object* v_ref_5415_; lean_object* v___x_5416_; lean_object* v_a_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
lean_dec(v_eq_x3f_5377_);
v_ref_5415_ = lean_ctor_get(v___y_5375_, 5);
v___x_5416_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5415_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc_n(v_a_5417_, 18);
lean_dec_ref(v___x_5416_);
v___x_5418_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5419_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5420_, 0, v_a_5417_);
lean_ctor_set(v___x_5420_, 1, v___x_5419_);
v___x_5421_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5422_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5423_, 0, v_a_5417_);
lean_ctor_set(v___x_5423_, 1, v___x_5421_);
lean_ctor_set(v___x_5423_, 2, v___x_5422_);
v___x_5424_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5423_, 3);
v___x_5425_ = l_Lean_Syntax_node2(v_a_5417_, v___x_5424_, v___x_5423_, v___y_5366_);
v___x_5426_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5421_, v___x_5425_);
v___x_5427_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5428_, 0, v_a_5417_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5430_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5431_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5432_, 0, v_a_5417_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5421_, v___y_5365_);
v___x_5434_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5421_, v___x_5433_);
v___x_5435_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5436_, 0, v_a_5417_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
lean_inc_ref(v___x_5436_);
lean_inc_ref(v___x_5432_);
v___x_5437_ = l_Lean_Syntax_node4(v_a_5417_, v___x_5430_, v___x_5432_, v___x_5434_, v___x_5436_, v_body_5369_);
v___x_5438_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5439_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5440_, 0, v_a_5417_);
lean_ctor_set(v___x_5440_, 1, v___x_5439_);
v___x_5441_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5438_, v___x_5440_);
v___x_5442_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5421_, v___x_5441_);
v___x_5443_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5421_, v___x_5442_);
v___x_5444_ = l_Lean_Syntax_node4(v_a_5417_, v___x_5430_, v___x_5432_, v___x_5443_, v___x_5436_, v___y_5368_);
v___x_5445_ = l_Lean_Syntax_node2(v_a_5417_, v___x_5421_, v___x_5437_, v___x_5444_);
v___x_5446_ = l_Lean_Syntax_node1(v_a_5417_, v___x_5429_, v___x_5445_);
v___x_5447_ = l_Lean_Syntax_node7(v_a_5417_, v___x_5418_, v___x_5420_, v___x_5423_, v___x_5423_, v___x_5423_, v___x_5426_, v___x_5428_, v___x_5446_);
v___x_5448_ = l_Lean_Elab_Do_elabDoElem(v___x_5447_, v_dec_5351_, v___x_5361_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
return v___x_5448_;
}
}
v___jp_5449_:
{
if (lean_obj_tag(v___y_5450_) == 0)
{
lean_dec_ref(v___y_5453_);
v___y_5364_ = v___y_5456_;
v___y_5365_ = v___y_5451_;
v___y_5366_ = v___y_5452_;
v___y_5367_ = v___y_5460_;
v___y_5368_ = v___y_5462_;
v_body_5369_ = v_a_5465_;
v___y_5370_ = v___y_5461_;
v___y_5371_ = v___y_5464_;
v___y_5372_ = v___y_5454_;
v___y_5373_ = v___y_5458_;
v___y_5374_ = v___y_5455_;
v___y_5375_ = v___y_5463_;
v___y_5376_ = v___y_5459_;
goto v___jp_5363_;
}
else
{
lean_dec_ref_known(v___y_5450_, 1);
if (v___y_5457_ == 0)
{
lean_dec_ref(v___y_5453_);
v___y_5364_ = v___y_5456_;
v___y_5365_ = v___y_5451_;
v___y_5366_ = v___y_5452_;
v___y_5367_ = v___y_5460_;
v___y_5368_ = v___y_5462_;
v_body_5369_ = v_a_5465_;
v___y_5370_ = v___y_5461_;
v___y_5371_ = v___y_5464_;
v___y_5372_ = v___y_5454_;
v___y_5373_ = v___y_5458_;
v___y_5374_ = v___y_5455_;
v___y_5375_ = v___y_5463_;
v___y_5376_ = v___y_5459_;
goto v___jp_5363_;
}
else
{
size_t v_sz_5466_; size_t v___x_5467_; lean_object* v___x_5468_; 
v_sz_5466_ = lean_array_size(v___y_5453_);
v___x_5467_ = ((size_t)0ULL);
v___x_5468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5453_, v_sz_5466_, v___x_5467_, v_a_5465_, v___y_5461_, v___y_5464_, v___y_5454_, v___y_5458_, v___y_5455_, v___y_5463_, v___y_5459_);
lean_dec_ref(v___y_5453_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
lean_inc(v_a_5469_);
lean_dec_ref_known(v___x_5468_, 1);
v___y_5364_ = v___y_5456_;
v___y_5365_ = v___y_5451_;
v___y_5366_ = v___y_5452_;
v___y_5367_ = v___y_5460_;
v___y_5368_ = v___y_5462_;
v_body_5369_ = v_a_5469_;
v___y_5370_ = v___y_5461_;
v___y_5371_ = v___y_5464_;
v___y_5372_ = v___y_5454_;
v___y_5373_ = v___y_5458_;
v___y_5374_ = v___y_5455_;
v___y_5375_ = v___y_5463_;
v___y_5376_ = v___y_5459_;
goto v___jp_5363_;
}
else
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5477_; 
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5452_);
lean_dec(v___y_5451_);
lean_dec_ref(v_dec_5351_);
v_a_5470_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5472_ = v___x_5468_;
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5468_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5475_; 
if (v_isShared_5473_ == 0)
{
v___x_5475_ = v___x_5472_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
}
}
v___jp_5478_:
{
uint8_t v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5493_ = 0;
v___x_5494_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5495_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5485_, v___y_5479_, v___x_5494_, v___y_5491_, v___y_5482_, v___y_5486_, v___y_5483_, v___y_5490_, v___y_5487_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5497_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v___x_5495_, 1);
v___x_5497_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5496_, v___y_5488_, v___y_5491_, v___y_5482_, v___y_5486_, v___y_5483_, v___y_5490_, v___y_5487_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v___x_5498_; 
lean_dec_ref_known(v___x_5497_, 1);
lean_inc(v___y_5480_);
v___x_5498_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5480_, v___y_5491_, v___y_5482_, v___y_5486_, v___y_5483_, v___y_5490_, v___y_5487_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
lean_inc(v_a_5499_);
lean_dec_ref_known(v___x_5498_, 1);
lean_inc(v___y_5479_);
v___x_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5500_, 0, v___y_5479_);
v___x_5501_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5500_, v_a_5499_, v___y_5488_, v___y_5491_, v___y_5482_, v___y_5486_, v___y_5483_, v___y_5490_, v___y_5487_);
lean_dec_ref_known(v___x_5500_, 1);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_dec_ref_known(v___x_5501_, 1);
if (lean_obj_tag(v___y_5492_) == 0)
{
lean_object* v_ref_5502_; lean_object* v_quotContext_5503_; lean_object* v_currMacroScope_5504_; lean_object* v___x_5505_; lean_object* v_a_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; 
v_ref_5502_ = lean_ctor_get(v___y_5490_, 5);
v_quotContext_5503_ = lean_ctor_get(v___y_5490_, 10);
v_currMacroScope_5504_ = lean_ctor_get(v___y_5490_, 11);
v___x_5505_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5502_, v___y_5488_, v___y_5491_, v___y_5482_, v___y_5486_, v___y_5483_, v___y_5490_, v___y_5487_);
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
lean_inc_n(v_a_5506_, 9);
lean_dec_ref(v___x_5505_);
v___x_5507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5508_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5511_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5512_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5513_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5504_, 2);
lean_inc_n(v_quotContext_5503_, 2);
v___x_5514_ = l_Lean_addMacroScope(v_quotContext_5503_, v___x_5513_, v_currMacroScope_5504_);
v___x_5515_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5516_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5516_, 0, v_a_5506_);
lean_ctor_set(v___x_5516_, 1, v___x_5512_);
lean_ctor_set(v___x_5516_, 2, v___x_5514_);
lean_ctor_set(v___x_5516_, 3, v___x_5515_);
v___x_5517_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5519_ = l_Lean_addMacroScope(v_quotContext_5503_, v___x_5518_, v_currMacroScope_5504_);
v___x_5520_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5521_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5521_, 0, v_a_5506_);
lean_ctor_set(v___x_5521_, 1, v___x_5517_);
lean_ctor_set(v___x_5521_, 2, v___x_5519_);
lean_ctor_set(v___x_5521_, 3, v___x_5520_);
v___x_5522_ = l_Lean_Syntax_node1(v_a_5506_, v___x_5508_, v___x_5521_);
v___x_5523_ = l_Lean_Syntax_node2(v_a_5506_, v___x_5511_, v___x_5516_, v___x_5522_);
v___x_5524_ = l_Lean_Syntax_node1(v_a_5506_, v___x_5510_, v___x_5523_);
v___x_5525_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5526_, 0, v_a_5506_);
lean_ctor_set(v___x_5526_, 1, v___x_5508_);
lean_ctor_set(v___x_5526_, 2, v___x_5525_);
v___x_5527_ = l_Lean_Syntax_node2(v_a_5506_, v___x_5509_, v___x_5524_, v___x_5526_);
v___x_5528_ = l_Lean_Syntax_node1(v_a_5506_, v___x_5508_, v___x_5527_);
v___x_5529_ = l_Lean_Syntax_node1(v_a_5506_, v___x_5507_, v___x_5528_);
v___y_5450_ = v___y_5479_;
v___y_5451_ = v___y_5480_;
v___y_5452_ = v___y_5481_;
v___y_5453_ = v_a_5499_;
v___y_5454_ = v___y_5482_;
v___y_5455_ = v___y_5483_;
v___y_5456_ = v___x_5493_;
v___y_5457_ = v___y_5484_;
v___y_5458_ = v___y_5486_;
v___y_5459_ = v___y_5487_;
v___y_5460_ = v_a_5496_;
v___y_5461_ = v___y_5488_;
v___y_5462_ = v___y_5489_;
v___y_5463_ = v___y_5490_;
v___y_5464_ = v___y_5491_;
v_a_5465_ = v___x_5529_;
goto v___jp_5449_;
}
else
{
lean_object* v_val_5530_; 
v_val_5530_ = lean_ctor_get(v___y_5492_, 0);
lean_inc(v_val_5530_);
lean_dec_ref_known(v___y_5492_, 1);
v___y_5450_ = v___y_5479_;
v___y_5451_ = v___y_5480_;
v___y_5452_ = v___y_5481_;
v___y_5453_ = v_a_5499_;
v___y_5454_ = v___y_5482_;
v___y_5455_ = v___y_5483_;
v___y_5456_ = v___x_5493_;
v___y_5457_ = v___y_5484_;
v___y_5458_ = v___y_5486_;
v___y_5459_ = v___y_5487_;
v___y_5460_ = v_a_5496_;
v___y_5461_ = v___y_5488_;
v___y_5462_ = v___y_5489_;
v___y_5463_ = v___y_5490_;
v___y_5464_ = v___y_5491_;
v_a_5465_ = v_val_5530_;
goto v___jp_5449_;
}
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec(v_a_5499_);
lean_dec(v_a_5496_);
lean_dec(v___y_5492_);
lean_dec(v___y_5489_);
lean_dec(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5351_);
v_a_5531_ = lean_ctor_get(v___x_5501_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5501_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5501_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5501_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec(v_a_5496_);
lean_dec(v___y_5492_);
lean_dec(v___y_5489_);
lean_dec(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5351_);
v_a_5539_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5498_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5498_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_dec(v_a_5496_);
lean_dec(v___y_5492_);
lean_dec(v___y_5489_);
lean_dec(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5351_);
v_a_5547_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5497_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5497_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec(v___y_5492_);
lean_dec(v___y_5489_);
lean_dec(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v_dec_5351_);
v_a_5555_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5495_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5495_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
v___jp_5563_:
{
lean_object* v___x_5572_; lean_object* v_cfg_5573_; lean_object* v___x_5574_; uint8_t v___x_5575_; 
v___x_5572_ = lean_unsigned_to_nat(2u);
v_cfg_5573_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5572_);
v___x_5574_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5573_);
v___x_5575_ = l_Lean_Syntax_isOfKind(v_cfg_5573_, v___x_5574_);
if (v___x_5575_ == 0)
{
lean_object* v___x_5576_; 
lean_dec(v_cfg_5573_);
lean_dec(v_mutTk_x3f_5564_);
lean_dec_ref(v_dec_5351_);
lean_dec(v_stx_5350_);
v___x_5576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5576_;
}
else
{
lean_object* v___x_5577_; lean_object* v_pattern_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5577_ = lean_unsigned_to_nat(3u);
v_pattern_5578_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5577_);
v___x_5579_ = lean_unsigned_to_nat(5u);
v___x_5580_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5579_);
v___x_5581_ = lean_unsigned_to_nat(7u);
v___x_5582_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5581_);
v___x_5583_ = lean_unsigned_to_nat(8u);
v___x_5584_ = l_Lean_Syntax_getArg(v_stx_5350_, v___x_5583_);
lean_dec(v_stx_5350_);
v___x_5585_ = l_Lean_Syntax_getOptional_x3f(v___x_5584_);
lean_dec(v___x_5584_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v___x_5586_; 
v___x_5586_ = lean_box(0);
v___y_5479_ = v_mutTk_x3f_5564_;
v___y_5480_ = v_pattern_5578_;
v___y_5481_ = v___x_5580_;
v___y_5482_ = v___y_5567_;
v___y_5483_ = v___y_5569_;
v___y_5484_ = v___x_5575_;
v___y_5485_ = v_cfg_5573_;
v___y_5486_ = v___y_5568_;
v___y_5487_ = v___y_5571_;
v___y_5488_ = v___y_5565_;
v___y_5489_ = v___x_5582_;
v___y_5490_ = v___y_5570_;
v___y_5491_ = v___y_5566_;
v___y_5492_ = v___x_5586_;
goto v___jp_5478_;
}
else
{
lean_object* v_val_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
v_val_5587_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5585_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_val_5587_);
lean_dec(v___x_5585_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_val_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
v___y_5479_ = v_mutTk_x3f_5564_;
v___y_5480_ = v_pattern_5578_;
v___y_5481_ = v___x_5580_;
v___y_5482_ = v___y_5567_;
v___y_5483_ = v___y_5569_;
v___y_5484_ = v___x_5575_;
v___y_5485_ = v_cfg_5573_;
v___y_5486_ = v___y_5568_;
v___y_5487_ = v___y_5571_;
v___y_5488_ = v___y_5565_;
v___y_5489_ = v___x_5582_;
v___y_5490_ = v___y_5570_;
v___y_5491_ = v___y_5566_;
v___y_5492_ = v___x_5592_;
goto v___jp_5478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5604_, lean_object* v_dec_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5604_, v_dec_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_);
lean_dec(v_a_5612_);
lean_dec_ref(v_a_5611_);
lean_dec(v_a_5610_);
lean_dec_ref(v_a_5609_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
lean_dec_ref(v_a_5606_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5615_, size_t v_sz_5616_, size_t v_i_5617_, lean_object* v_b_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_){
_start:
{
lean_object* v___x_5627_; 
v___x_5627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5615_, v_sz_5616_, v_i_5617_, v_b_5618_, v___y_5624_);
return v___x_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5628_, lean_object* v_sz_5629_, lean_object* v_i_5630_, lean_object* v_b_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
size_t v_sz_boxed_5640_; size_t v_i_boxed_5641_; lean_object* v_res_5642_; 
v_sz_boxed_5640_ = lean_unbox_usize(v_sz_5629_);
lean_dec(v_sz_5629_);
v_i_boxed_5641_ = lean_unbox_usize(v_i_5630_);
lean_dec(v_i_5630_);
v_res_5642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5628_, v_sz_boxed_5640_, v_i_boxed_5641_, v_b_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec_ref(v_as_5628_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v___x_5650_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5651_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5653_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5654_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5650_, v___x_5651_, v___x_5652_, v___x_5653_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5656_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5664_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5665_ = l_Lean_stringToMessageData(v___x_5664_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5666_, lean_object* v_dec_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_){
_start:
{
lean_object* v___x_5676_; uint8_t v___x_5677_; 
v___x_5676_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5666_);
v___x_5677_ = l_Lean_Syntax_isOfKind(v_stx_5666_, v___x_5676_);
if (v___x_5677_ == 0)
{
lean_object* v___x_5678_; 
lean_dec_ref(v_dec_5667_);
lean_dec(v_stx_5666_);
v___x_5678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5678_;
}
else
{
lean_object* v___x_5679_; lean_object* v_tk_5680_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; uint8_t v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; uint8_t v___y_5727_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; uint8_t v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; uint8_t v___y_5742_; lean_object* v_mutTk_x3f_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v___y_5751_; lean_object* v___y_5752_; lean_object* v___x_5782_; lean_object* v___x_5783_; uint8_t v___x_5784_; 
v___x_5679_ = lean_unsigned_to_nat(0u);
v_tk_5680_ = l_Lean_Syntax_getArg(v_stx_5666_, v___x_5679_);
v___x_5782_ = lean_unsigned_to_nat(1u);
v___x_5783_ = l_Lean_Syntax_getArg(v_stx_5666_, v___x_5782_);
v___x_5784_ = l_Lean_Syntax_isNone(v___x_5783_);
if (v___x_5784_ == 0)
{
uint8_t v___x_5785_; 
lean_inc(v___x_5783_);
v___x_5785_ = l_Lean_Syntax_matchesNull(v___x_5783_, v___x_5782_);
if (v___x_5785_ == 0)
{
lean_object* v___x_5786_; 
lean_dec(v___x_5783_);
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
lean_dec(v_stx_5666_);
v___x_5786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5786_;
}
else
{
lean_object* v_mutTk_x3f_5787_; lean_object* v___x_5788_; 
v_mutTk_x3f_5787_ = l_Lean_Syntax_getArg(v___x_5783_, v___x_5679_);
lean_dec(v___x_5783_);
v___x_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5788_, 0, v_mutTk_x3f_5787_);
v_mutTk_x3f_5745_ = v___x_5788_;
v___y_5746_ = v_a_5668_;
v___y_5747_ = v_a_5669_;
v___y_5748_ = v_a_5670_;
v___y_5749_ = v_a_5671_;
v___y_5750_ = v_a_5672_;
v___y_5751_ = v_a_5673_;
v___y_5752_ = v_a_5674_;
goto v___jp_5744_;
}
}
else
{
lean_object* v___x_5789_; 
lean_dec(v___x_5783_);
v___x_5789_ = lean_box(0);
v_mutTk_x3f_5745_ = v___x_5789_;
v___y_5746_ = v_a_5668_;
v___y_5747_ = v_a_5669_;
v___y_5748_ = v_a_5670_;
v___y_5749_ = v_a_5671_;
v___y_5750_ = v_a_5672_;
v___y_5751_ = v_a_5673_;
v___y_5752_ = v_a_5674_;
goto v___jp_5744_;
}
v___jp_5681_:
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5691_, 0, v___y_5682_);
v___x_5692_ = l_Lean_Elab_Do_elabDoArrow(v___x_5691_, v___y_5683_, v_tk_5680_, v_dec_5667_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
lean_dec(v_tk_5680_);
return v___x_5692_;
}
v___jp_5693_:
{
lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v_a_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5713_; 
lean_dec(v___y_5701_);
lean_dec(v___y_5697_);
v___x_5704_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5705_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5699_, v___x_5704_, v___y_5703_, v___y_5698_, v___y_5695_, v___y_5694_);
lean_dec(v___y_5699_);
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
v_isSharedCheck_5713_ = !lean_is_exclusive(v___x_5705_);
if (v_isSharedCheck_5713_ == 0)
{
v___x_5708_ = v___x_5705_;
v_isShared_5709_ = v_isSharedCheck_5713_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_a_5706_);
lean_dec(v___x_5705_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5713_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v___x_5711_; 
if (v_isShared_5709_ == 0)
{
v___x_5711_ = v___x_5708_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_a_5706_);
v___x_5711_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
return v___x_5711_;
}
}
}
v___jp_5714_:
{
if (v___y_5727_ == 0)
{
lean_object* v_eq_x3f_5728_; 
v_eq_x3f_5728_ = lean_ctor_get(v___y_5726_, 0);
lean_inc(v_eq_x3f_5728_);
lean_dec_ref(v___y_5726_);
if (lean_obj_tag(v_eq_x3f_5728_) == 0)
{
lean_dec(v___y_5723_);
v___y_5682_ = v___y_5721_;
v___y_5683_ = v___y_5717_;
v___y_5684_ = v___y_5725_;
v___y_5685_ = v___y_5716_;
v___y_5686_ = v___y_5724_;
v___y_5687_ = v___y_5719_;
v___y_5688_ = v___y_5722_;
v___y_5689_ = v___y_5720_;
v___y_5690_ = v___y_5715_;
goto v___jp_5681_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5728_, 1);
if (v___y_5718_ == 0)
{
lean_dec(v___y_5723_);
v___y_5682_ = v___y_5721_;
v___y_5683_ = v___y_5717_;
v___y_5684_ = v___y_5725_;
v___y_5685_ = v___y_5716_;
v___y_5686_ = v___y_5724_;
v___y_5687_ = v___y_5719_;
v___y_5688_ = v___y_5722_;
v___y_5689_ = v___y_5720_;
v___y_5690_ = v___y_5715_;
goto v___jp_5681_;
}
else
{
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
v___y_5694_ = v___y_5715_;
v___y_5695_ = v___y_5720_;
v___y_5696_ = v___y_5716_;
v___y_5697_ = v___y_5721_;
v___y_5698_ = v___y_5722_;
v___y_5699_ = v___y_5723_;
v___y_5700_ = v___y_5724_;
v___y_5701_ = v___y_5717_;
v___y_5702_ = v___y_5725_;
v___y_5703_ = v___y_5719_;
goto v___jp_5693_;
}
}
}
else
{
lean_dec_ref(v___y_5726_);
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
v___y_5694_ = v___y_5715_;
v___y_5695_ = v___y_5720_;
v___y_5696_ = v___y_5716_;
v___y_5697_ = v___y_5721_;
v___y_5698_ = v___y_5722_;
v___y_5699_ = v___y_5723_;
v___y_5700_ = v___y_5724_;
v___y_5701_ = v___y_5717_;
v___y_5702_ = v___y_5725_;
v___y_5703_ = v___y_5719_;
goto v___jp_5693_;
}
}
v___jp_5729_:
{
if (v___y_5742_ == 0)
{
uint8_t v_zeta_5743_; 
v_zeta_5743_ = lean_ctor_get_uint8(v___y_5741_, sizeof(void*)*1 + 2);
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5731_;
v___y_5717_ = v___y_5732_;
v___y_5718_ = v___y_5733_;
v___y_5719_ = v___y_5734_;
v___y_5720_ = v___y_5735_;
v___y_5721_ = v___y_5736_;
v___y_5722_ = v___y_5737_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5739_;
v___y_5725_ = v___y_5740_;
v___y_5726_ = v___y_5741_;
v___y_5727_ = v_zeta_5743_;
goto v___jp_5714_;
}
else
{
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5731_;
v___y_5717_ = v___y_5732_;
v___y_5718_ = v___y_5733_;
v___y_5719_ = v___y_5734_;
v___y_5720_ = v___y_5735_;
v___y_5721_ = v___y_5736_;
v___y_5722_ = v___y_5737_;
v___y_5723_ = v___y_5738_;
v___y_5724_ = v___y_5739_;
v___y_5725_ = v___y_5740_;
v___y_5726_ = v___y_5741_;
v___y_5727_ = v___x_5677_;
goto v___jp_5714_;
}
}
v___jp_5744_:
{
lean_object* v___x_5753_; lean_object* v_cfg_5754_; lean_object* v___x_5755_; uint8_t v___x_5756_; 
v___x_5753_ = lean_unsigned_to_nat(2u);
v_cfg_5754_ = l_Lean_Syntax_getArg(v_stx_5666_, v___x_5753_);
v___x_5755_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5754_);
v___x_5756_ = l_Lean_Syntax_isOfKind(v_cfg_5754_, v___x_5755_);
if (v___x_5756_ == 0)
{
lean_object* v___x_5757_; 
lean_dec(v_cfg_5754_);
lean_dec(v_mutTk_x3f_5745_);
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
lean_dec(v_stx_5666_);
v___x_5757_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5757_;
}
else
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5754_);
v___x_5759_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5754_, v_mutTk_x3f_5745_, v___x_5758_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v___x_5761_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_a_5760_);
lean_dec_ref_known(v___x_5759_, 1);
v___x_5761_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5760_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
if (lean_obj_tag(v___x_5761_) == 0)
{
uint8_t v_nondep_5762_; uint8_t v_usedOnly_5763_; lean_object* v___x_5764_; lean_object* v_decl_5765_; 
lean_dec_ref_known(v___x_5761_, 1);
v_nondep_5762_ = lean_ctor_get_uint8(v_a_5760_, sizeof(void*)*1);
v_usedOnly_5763_ = lean_ctor_get_uint8(v_a_5760_, sizeof(void*)*1 + 1);
v___x_5764_ = lean_unsigned_to_nat(3u);
v_decl_5765_ = l_Lean_Syntax_getArg(v_stx_5666_, v___x_5764_);
lean_dec(v_stx_5666_);
if (v_nondep_5762_ == 0)
{
v___y_5730_ = v___y_5752_;
v___y_5731_ = v___y_5747_;
v___y_5732_ = v_decl_5765_;
v___y_5733_ = v___x_5756_;
v___y_5734_ = v___y_5749_;
v___y_5735_ = v___y_5751_;
v___y_5736_ = v_mutTk_x3f_5745_;
v___y_5737_ = v___y_5750_;
v___y_5738_ = v_cfg_5754_;
v___y_5739_ = v___y_5748_;
v___y_5740_ = v___y_5746_;
v___y_5741_ = v_a_5760_;
v___y_5742_ = v_usedOnly_5763_;
goto v___jp_5729_;
}
else
{
v___y_5730_ = v___y_5752_;
v___y_5731_ = v___y_5747_;
v___y_5732_ = v_decl_5765_;
v___y_5733_ = v___x_5756_;
v___y_5734_ = v___y_5749_;
v___y_5735_ = v___y_5751_;
v___y_5736_ = v_mutTk_x3f_5745_;
v___y_5737_ = v___y_5750_;
v___y_5738_ = v_cfg_5754_;
v___y_5739_ = v___y_5748_;
v___y_5740_ = v___y_5746_;
v___y_5741_ = v_a_5760_;
v___y_5742_ = v___x_5677_;
goto v___jp_5729_;
}
}
else
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5773_; 
lean_dec(v_a_5760_);
lean_dec(v_cfg_5754_);
lean_dec(v_mutTk_x3f_5745_);
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
lean_dec(v_stx_5666_);
v_a_5766_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5768_ = v___x_5761_;
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5761_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5771_; 
if (v_isShared_5769_ == 0)
{
v___x_5771_ = v___x_5768_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5766_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
}
else
{
lean_object* v_a_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5781_; 
lean_dec(v_cfg_5754_);
lean_dec(v_mutTk_x3f_5745_);
lean_dec(v_tk_5680_);
lean_dec_ref(v_dec_5667_);
lean_dec(v_stx_5666_);
v_a_5774_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5776_ = v___x_5759_;
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_a_5774_);
lean_dec(v___x_5759_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5779_; 
if (v_isShared_5777_ == 0)
{
v___x_5779_ = v___x_5776_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5774_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
return v___x_5779_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5790_, lean_object* v_dec_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5790_, v_dec_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_);
lean_dec(v_a_5798_);
lean_dec_ref(v_a_5797_);
lean_dec(v_a_5796_);
lean_dec_ref(v_a_5795_);
lean_dec(v_a_5794_);
lean_dec_ref(v_a_5793_);
lean_dec_ref(v_a_5792_);
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5808_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5809_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5810_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5811_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5812_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5808_, v___x_5809_, v___x_5810_, v___x_5811_);
return v___x_5812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5821_, lean_object* v_dec_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v___x_5831_; uint8_t v___x_5832_; 
v___x_5831_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5821_);
v___x_5832_ = l_Lean_Syntax_isOfKind(v_stx_5821_, v___x_5831_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; 
lean_dec_ref(v_dec_5822_);
lean_dec(v_stx_5821_);
v___x_5833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5833_;
}
else
{
lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; uint8_t v___x_5837_; 
v___x_5834_ = lean_unsigned_to_nat(0u);
v___x_5835_ = l_Lean_Syntax_getArg(v_stx_5821_, v___x_5834_);
lean_dec(v_stx_5821_);
v___x_5836_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5835_);
v___x_5837_ = l_Lean_Syntax_isOfKind(v___x_5835_, v___x_5836_);
if (v___x_5837_ == 0)
{
lean_object* v___x_5838_; uint8_t v___x_5839_; 
v___x_5838_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5835_);
v___x_5839_ = l_Lean_Syntax_isOfKind(v___x_5835_, v___x_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; 
lean_dec(v___x_5835_);
lean_dec_ref(v_dec_5822_);
v___x_5840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5840_;
}
else
{
lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5841_ = lean_box(2);
lean_inc(v___x_5835_);
v___x_5842_ = l_Lean_Elab_Do_elabDoArrow(v___x_5841_, v___x_5835_, v___x_5835_, v_dec_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
lean_dec(v___x_5835_);
return v___x_5842_;
}
}
else
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = lean_box(2);
lean_inc(v___x_5835_);
v___x_5844_ = l_Lean_Elab_Do_elabDoArrow(v___x_5843_, v___x_5835_, v___x_5835_, v_dec_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
lean_dec(v___x_5835_);
return v___x_5844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5845_, lean_object* v_dec_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5845_, v_dec_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_);
lean_dec(v_a_5853_);
lean_dec_ref(v_a_5852_);
lean_dec(v_a_5851_);
lean_dec_ref(v_a_5850_);
lean_dec(v_a_5849_);
lean_dec_ref(v_a_5848_);
lean_dec_ref(v_a_5847_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5863_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5864_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5865_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5866_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5867_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5863_, v___x_5864_, v___x_5865_, v___x_5866_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5869_;
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
