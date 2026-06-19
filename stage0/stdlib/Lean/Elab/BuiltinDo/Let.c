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
lean_object* l_Lean_Elab_Do_findMutVar_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Do_MutVar_mkAliasInfo(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(lean_object* v_t_75_, lean_object* v___y_76_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg___boxed(lean_object* v_t_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_t_115_, v___y_116_);
lean_dec(v___y_116_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0(void){
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
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1(void){
_start:
{
size_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_122_ = ((size_t)5ULL);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_unsigned_to_nat(32u);
v___x_125_ = lean_mk_empty_array_with_capacity(v___x_124_);
v___x_126_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__0);
v___x_127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_123_);
lean_ctor_set(v___x_127_, 3, v___x_123_);
lean_ctor_set_usize(v___x_127_, 4, v___x_122_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_t_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
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
v___x_142_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v_t_128_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v___x_143_, v___y_135_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_t_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_t_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(lean_object* v_as_155_, size_t v_sz_156_, size_t v_i_157_, lean_object* v_b_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_a_168_; uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_157_, v_sz_156_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_b_158_);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_a_174_ = lean_array_uget_borrowed(v_as_155_, v_i_157_);
v___x_175_ = l_Lean_TSyntax_getId(v_a_174_);
v___x_176_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_175_, v___y_159_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
v___x_178_ = lean_box(0);
if (lean_obj_tag(v_a_177_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_201_; 
v_val_179_ = lean_ctor_get(v_a_177_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_a_177_);
if (v_isSharedCheck_201_ == 0)
{
v___x_181_ = v_a_177_;
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_a_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_201_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_getFVarFromUserName(v___x_175_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v_baseId_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v_baseId_185_ = lean_ctor_get(v_val_179_, 1);
v___x_186_ = l_Lean_Expr_fvarId_x21(v_a_184_);
lean_dec(v_a_184_);
v___x_187_ = l_Lean_instBEqFVarId_beq(v___x_186_, v_baseId_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = l_Lean_Elab_Do_MutVar_mkAliasInfo(v_val_179_, v___x_186_);
lean_dec(v_val_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 11);
lean_ctor_set(v___x_181_, 0, v___x_188_);
v___x_190_ = v___x_181_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v___x_190_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_dec_ref_known(v___x_191_, 1);
v_a_168_ = v___x_178_;
goto v___jp_167_;
}
else
{
return v___x_191_;
}
}
}
else
{
lean_dec(v___x_186_);
lean_del_object(v___x_181_);
lean_dec(v_val_179_);
v_a_168_ = v___x_178_;
goto v___jp_167_;
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_del_object(v___x_181_);
lean_dec(v_val_179_);
v_a_193_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_183_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_183_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_dec(v_a_177_);
lean_dec(v___x_175_);
v_a_168_ = v___x_178_;
goto v___jp_167_;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v___x_175_);
v_a_202_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_176_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_176_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
v___jp_167_:
{
size_t v___x_169_; size_t v___x_170_; 
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_157_, v___x_169_);
v_i_157_ = v___x_170_;
v_b_158_ = v_a_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1___boxed(lean_object* v_as_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_223_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v_as_210_, v_sz_boxed_222_, v_i_boxed_223_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_225_, lean_object* v_vars_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
if (lean_obj_tag(v_letOrReassign_225_) == 2)
{
lean_object* v___x_235_; size_t v_sz_236_; size_t v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_box(0);
v_sz_236_ = lean_array_size(v_vars_226_);
v___x_237_ = ((size_t)0ULL);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__1(v_vars_226_, v_sz_236_, v___x_237_, v___x_235_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_238_, 0);
lean_dec(v_unused_246_);
v___x_240_ = v___x_238_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_dec(v___x_238_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_235_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_235_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
return v___x_238_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_249_, lean_object* v_vars_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_249_, v_vars_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_vars_250_);
lean_dec(v_letOrReassign_249_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(lean_object* v_t_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___redArg(v_t_260_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0___boxed(lean_object* v_t_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0_spec__0(v_t_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(lean_object* v_elabBody_280_, lean_object* v_body_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
v___x_290_ = lean_apply_8(v_elabBody_280_, v_body_281_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed(lean_object* v_elabBody_291_, lean_object* v_body_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0(v_elabBody_291_, v_body_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(lean_object* v_letOrReassign_302_, lean_object* v_vars_303_, lean_object* v_k_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_302_, v_vars_303_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_314_; 
lean_dec_ref_known(v___x_313_, 1);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_314_ = lean_apply_8(v_k_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, lean_box(0));
return v___x_314_;
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_k_304_);
v_a_315_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_313_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed(lean_object* v_letOrReassign_323_, lean_object* v_vars_324_, lean_object* v_k_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1(v_letOrReassign_323_, v_vars_324_, v_k_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec_ref(v_vars_324_);
lean_dec(v_letOrReassign_323_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith(lean_object* v_hint_335_, lean_object* v_letOrReassign_336_, lean_object* v_vars_337_, lean_object* v_k_338_, lean_object* v_elabBody_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v_elabCont_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__0___boxed), 10, 1);
lean_closure_set(v___f_348_, 0, v_elabBody_339_);
lean_inc_ref(v_vars_337_);
lean_inc(v_letOrReassign_336_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_349_, 0, v_letOrReassign_336_);
lean_closure_set(v___f_349_, 1, v_vars_337_);
lean_closure_set(v___f_349_, 2, v_k_338_);
v___x_350_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_336_);
lean_dec(v_letOrReassign_336_);
v_elabCont_351_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVars_x3f___boxed), 12, 4);
lean_closure_set(v_elabCont_351_, 0, lean_box(0));
lean_closure_set(v_elabCont_351_, 1, v___x_350_);
lean_closure_set(v_elabCont_351_, 2, v_vars_337_);
lean_closure_set(v_elabCont_351_, 3, v___f_349_);
v___x_352_ = lean_box(0);
v___x_353_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v_hint_335_, v_elabCont_351_, v___f_348_, v___x_352_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassignWith___boxed(lean_object* v_hint_354_, lean_object* v_letOrReassign_355_, lean_object* v_vars_356_, lean_object* v_k_357_, lean_object* v_elabBody_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Elab_Do_elabDoLetOrReassignWith(v_hint_354_, v_letOrReassign_355_, v_vars_356_, v_k_357_, v_elabBody_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_368_, lean_object* v_vars_369_, lean_object* v_k_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_inc_ref(v_vars_369_);
lean_inc(v_letOrReassign_368_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassignWith___lam__1___boxed), 11, 3);
lean_closure_set(v___f_379_, 0, v_letOrReassign_368_);
lean_closure_set(v___f_379_, 1, v_vars_369_);
lean_closure_set(v___f_379_, 2, v_k_370_);
v___x_380_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_368_);
lean_dec(v_letOrReassign_368_);
v___x_381_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_380_, v_vars_369_, v___f_379_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_382_, lean_object* v_vars_383_, lean_object* v_k_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_382_, v_vars_383_, v_k_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_412_, lean_object* v_a_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_422_, lean_object* v_a_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_422_, v_a_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_env_439_; lean_object* v___x_440_; lean_object* v_mctx_441_; lean_object* v_lctx_442_; lean_object* v_options_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_438_ = lean_st_ref_get(v___y_436_);
v_env_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_env_439_);
lean_dec(v___x_438_);
v___x_440_ = lean_st_ref_get(v___y_434_);
v_mctx_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc_ref(v_mctx_441_);
lean_dec(v___x_440_);
v_lctx_442_ = lean_ctor_get(v___y_433_, 2);
v_options_443_ = lean_ctor_get(v___y_435_, 2);
lean_inc_ref(v_options_443_);
lean_inc_ref(v_lctx_442_);
v___x_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_444_, 0, v_env_439_);
lean_ctor_set(v___x_444_, 1, v_mctx_441_);
lean_ctor_set(v___x_444_, 2, v_lctx_442_);
lean_ctor_set(v___x_444_, 3, v_options_443_);
v___x_445_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_msgData_432_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_box(1);
v___x_455_ = l_Lean_MessageData_ofFormat(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__2));
v___x_460_ = l_Lean_MessageData_ofFormat(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
return v_x_461_;
}
else
{
lean_object* v_head_463_; lean_object* v_tail_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_486_; 
v_head_463_ = lean_ctor_get(v_x_462_, 0);
v_tail_464_ = lean_ctor_get(v_x_462_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_486_ == 0)
{
v___x_466_ = v_x_462_;
v_isShared_467_ = v_isSharedCheck_486_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_tail_464_);
lean_inc(v_head_463_);
lean_dec(v_x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_486_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_before_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_484_; 
v_before_468_ = lean_ctor_get(v_head_463_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_head_463_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v_head_463_, 1);
lean_dec(v_unused_485_);
v___x_470_ = v_head_463_;
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_before_468_);
lean_dec(v_head_463_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 7);
lean_ctor_set(v___x_470_, 1, v___x_472_);
lean_ctor_set(v___x_470_, 0, v_x_461_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_x_461_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_483_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 7);
lean_ctor_set(v___x_466_, 1, v___x_475_);
lean_ctor_set(v___x_466_, 0, v___x_474_);
v___x_477_ = v___x_466_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_482_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = l_Lean_MessageData_ofSyntax(v_before_468_);
v___x_479_ = l_Lean_indentD(v___x_478_);
v___x_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_477_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v_x_461_ = v___x_480_;
v_x_462_ = v_tail_464_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(lean_object* v_opts_487_, lean_object* v_opt_488_){
_start:
{
lean_object* v_name_489_; lean_object* v_defValue_490_; lean_object* v_map_491_; lean_object* v___x_492_; 
v_name_489_ = lean_ctor_get(v_opt_488_, 0);
v_defValue_490_ = lean_ctor_get(v_opt_488_, 1);
v_map_491_ = lean_ctor_get(v_opts_487_, 0);
v___x_492_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_491_, v_name_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
uint8_t v___x_493_; 
v___x_493_ = lean_unbox(v_defValue_490_);
return v___x_493_;
}
else
{
lean_object* v_val_494_; 
v_val_494_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v___x_492_, 1);
if (lean_obj_tag(v_val_494_) == 1)
{
uint8_t v_v_495_; 
v_v_495_ = lean_ctor_get_uint8(v_val_494_, 0);
lean_dec_ref_known(v_val_494_, 0);
return v_v_495_;
}
else
{
uint8_t v___x_496_; 
lean_dec(v_val_494_);
v___x_496_ = lean_unbox(v_defValue_490_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_497_, lean_object* v_opt_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_opts_497_, v_opt_498_);
lean_dec_ref(v_opt_498_);
lean_dec_ref(v_opts_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__1));
v___x_505_ = l_Lean_MessageData_ofFormat(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(lean_object* v_msgData_506_, lean_object* v_macroStack_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_options_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_options_510_ = lean_ctor_get(v___y_508_, 2);
v___x_511_ = l_Lean_Elab_pp_macroStack;
v___x_512_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__3(v_options_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_macroStack_507_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_msgData_506_);
return v___x_513_;
}
else
{
if (lean_obj_tag(v_macroStack_507_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_msgData_506_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_after_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_531_; 
v_head_515_ = lean_ctor_get(v_macroStack_507_, 0);
lean_inc(v_head_515_);
v_after_516_ = lean_ctor_get(v_head_515_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_head_515_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_head_515_, 0);
lean_dec(v_unused_532_);
v___x_518_ = v_head_515_;
v_isShared_519_ = v_isSharedCheck_531_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_after_516_);
lean_dec(v_head_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_531_;
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
lean_ctor_set(v___x_518_, 0, v_msgData_506_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_msgData_506_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_530_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_msgData_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___closed__2);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_MessageData_ofSyntax(v_after_516_);
v___x_526_ = l_Lean_indentD(v___x_525_);
v_msgData_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_527_, 0, v___x_524_);
lean_ctor_set(v_msgData_527_, 1, v___x_526_);
v___x_528_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1_spec__4(v_msgData_527_, v_macroStack_507_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_533_, lean_object* v_macroStack_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_533_, v_macroStack_534_, v___y_535_);
lean_dec_ref(v___y_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_ref_546_; lean_object* v___x_547_; lean_object* v_a_548_; lean_object* v_macroStack_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_ref_546_ = lean_ctor_get(v___y_543_, 5);
v___x_547_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_538_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
v_macroStack_549_ = lean_ctor_get(v___y_539_, 1);
v___x_550_ = l_Lean_Elab_getBetterRef(v_ref_546_, v_macroStack_549_);
lean_inc(v_macroStack_549_);
v___x_551_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_a_548_, v_macroStack_549_, v___y_543_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_550_);
lean_ctor_set(v___x_556_, 1, v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Array_mkArray0(lean_box(0));
return v___x_597_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_617_ = l_String_toRawSubstring_x27(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_664_, lean_object* v_decl_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
if (lean_obj_tag(v_letOrReassign_664_) == 2)
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_665_);
v___x_674_ = l_Lean_Syntax_isOfKind(v_decl_665_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_676_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_677_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = l_Lean_Syntax_getArg(v_decl_665_, v___x_679_);
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_680_);
v___x_682_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___y_685_; lean_object* v_pattern_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint8_t v___x_755_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_680_);
v___x_755_ = l_Lean_Syntax_isOfKind(v___x_680_, v___x_683_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v___x_680_);
v___x_756_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_757_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_758_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = l_Lean_Syntax_getArg(v___x_680_, v___x_760_);
v___x_762_ = l_Lean_Syntax_matchesNull(v___x_761_, v___x_679_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v___x_680_);
v___x_763_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_764_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_765_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_766_;
}
else
{
lean_object* v_pattern_767_; lean_object* v_xType_x3f_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_pattern_767_ = l_Lean_Syntax_getArg(v___x_680_, v___x_679_);
v___x_802_ = lean_unsigned_to_nat(2u);
v___x_803_ = l_Lean_Syntax_getArg(v___x_680_, v___x_802_);
v___x_804_ = l_Lean_Syntax_isNone(v___x_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
lean_inc(v___x_803_);
v___x_805_ = l_Lean_Syntax_matchesNull(v___x_803_, v___x_760_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___x_803_);
lean_dec(v_pattern_767_);
lean_dec(v___x_680_);
v___x_806_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_807_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_808_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = l_Lean_Syntax_getArg(v___x_803_, v___x_679_);
lean_dec(v___x_803_);
v___x_811_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_810_);
v___x_812_ = l_Lean_Syntax_isOfKind(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v___x_810_);
lean_dec(v_pattern_767_);
lean_dec(v___x_680_);
v___x_813_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_814_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_815_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_816_;
}
else
{
lean_object* v_xType_x3f_817_; lean_object* v___x_818_; 
lean_dec(v_decl_665_);
v_xType_x3f_817_ = l_Lean_Syntax_getArg(v___x_810_, v___x_760_);
lean_dec(v___x_810_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_xType_x3f_817_);
v_xType_x3f_769_ = v___x_818_;
v___y_770_ = v_a_666_;
v___y_771_ = v_a_667_;
v___y_772_ = v_a_668_;
v___y_773_ = v_a_669_;
v___y_774_ = v_a_670_;
v___y_775_ = v_a_671_;
goto v___jp_768_;
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v___x_803_);
lean_dec(v_decl_665_);
v___x_819_ = lean_box(0);
v_xType_x3f_769_ = v___x_819_;
v___y_770_ = v_a_666_;
v___y_771_ = v_a_667_;
v___y_772_ = v_a_668_;
v___y_773_ = v_a_669_;
v___y_774_ = v_a_670_;
v___y_775_ = v_a_671_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = l_Lean_Syntax_getArg(v___x_680_, v___x_776_);
lean_dec(v___x_680_);
if (lean_obj_tag(v_xType_x3f_769_) == 0)
{
v___y_685_ = v___x_777_;
v_pattern_686_ = v_pattern_767_;
v___y_687_ = v___y_770_;
v___y_688_ = v___y_771_;
v___y_689_ = v___y_772_;
v___y_690_ = v___y_773_;
v___y_691_ = v___y_774_;
v___y_692_ = v___y_775_;
goto v___jp_684_;
}
else
{
lean_object* v_val_778_; lean_object* v_ref_779_; lean_object* v_quotContext_780_; lean_object* v_currMacroScope_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_val_778_ = lean_ctor_get(v_xType_x3f_769_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_xType_x3f_769_, 1);
v_ref_779_ = lean_ctor_get(v___y_774_, 5);
v_quotContext_780_ = lean_ctor_get(v___y_774_, 10);
v_currMacroScope_781_ = lean_ctor_get(v___y_774_, 11);
v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_779_, v___x_682_);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_782_, 7);
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_782_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_788_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_789_ = lean_box(0);
lean_inc(v_currMacroScope_781_);
lean_inc(v_quotContext_780_);
v___x_790_ = l_Lean_addMacroScope(v_quotContext_780_, v___x_789_, v_currMacroScope_781_);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_792_, 0, v___x_782_);
lean_ctor_set(v___x_792_, 1, v___x_788_);
lean_ctor_set(v___x_792_, 2, v___x_790_);
lean_ctor_set(v___x_792_, 3, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v___x_782_, v___x_787_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node2(v___x_782_, v___x_784_, v___x_786_, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_782_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_798_ = l_Lean_Syntax_node1(v___x_782_, v___x_797_, v_val_778_);
v___x_799_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_782_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_Syntax_node5(v___x_782_, v___x_783_, v___x_794_, v_pattern_767_, v___x_796_, v___x_798_, v___x_800_);
v___y_685_ = v___x_777_;
v_pattern_686_ = v___x_801_;
v___y_687_ = v___y_770_;
v___y_688_ = v___y_771_;
v___y_689_ = v___y_772_;
v___y_690_ = v___y_773_;
v___y_691_ = v___y_774_;
v___y_692_ = v___y_775_;
goto v___jp_684_;
}
}
}
}
v___jp_684_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_box(v___x_674_);
v___x_695_ = lean_box(v___x_674_);
lean_inc(v_pattern_686_);
v___x_696_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_696_, 0, v_pattern_686_);
lean_closure_set(v___x_696_, 1, v___x_693_);
lean_closure_set(v___x_696_, 2, v___x_694_);
lean_closure_set(v___x_696_, 3, v___x_695_);
v___x_697_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_696_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_699_ = lean_infer_type(v_a_698_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_Elab_Term_exprToSyntax(v_a_700_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_738_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_738_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_738_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_738_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_ref_706_; lean_object* v_quotContext_707_; lean_object* v_currMacroScope_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_ref_706_ = lean_ctor_get(v___y_691_, 5);
v_quotContext_707_ = lean_ctor_get(v___y_691_, 10);
v_currMacroScope_708_ = lean_ctor_get(v___y_691_, 11);
v___x_709_ = l_Lean_SourceInfo_fromRef(v_ref_706_, v___x_682_);
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_711_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_709_, 11);
v___x_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_709_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
v___x_713_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_709_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_709_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_721_ = lean_box(0);
lean_inc(v_currMacroScope_708_);
lean_inc(v_quotContext_707_);
v___x_722_ = l_Lean_addMacroScope(v_quotContext_707_, v___x_721_, v_currMacroScope_708_);
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v___x_709_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
lean_ctor_set(v___x_724_, 2, v___x_722_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
v___x_725_ = l_Lean_Syntax_node1(v___x_709_, v___x_719_, v___x_724_);
v___x_726_ = l_Lean_Syntax_node2(v___x_709_, v___x_716_, v___x_718_, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_709_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_Syntax_node1(v___x_709_, v___x_710_, v_a_702_);
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_709_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_Syntax_node5(v___x_709_, v___x_715_, v___x_726_, v___y_685_, v___x_728_, v___x_729_, v___x_731_);
lean_inc_ref(v___x_712_);
v___x_733_ = l_Lean_Syntax_node5(v___x_709_, v___x_683_, v_pattern_686_, v___x_712_, v___x_712_, v___x_714_, v___x_732_);
v___x_734_ = l_Lean_Syntax_node1(v___x_709_, v___x_673_, v___x_733_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_734_);
v___x_736_ = v___x_704_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_dec(v_pattern_686_);
lean_dec(v___y_685_);
return v___x_701_;
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_pattern_686_);
lean_dec(v___y_685_);
v_a_739_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_699_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_699_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_pattern_686_);
lean_dec(v___y_685_);
v_a_747_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_697_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_697_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = l_Lean_Syntax_getArg(v___x_680_, v___x_679_);
v___x_821_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_820_);
v___x_822_ = l_Lean_Syntax_isOfKind(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v___x_820_);
lean_dec(v___x_680_);
v___x_823_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_824_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_825_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_826_;
}
else
{
lean_object* v_x_827_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_a_836_; lean_object* v_xType_x3f_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_x_827_ = l_Lean_Syntax_getArg(v___x_820_, v___x_679_);
lean_dec(v___x_820_);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_827_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_x_827_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_x_827_);
lean_dec(v___x_680_);
v___x_915_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_916_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_917_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = l_Lean_Syntax_getArg(v___x_680_, v___x_919_);
v___x_921_ = l_Lean_Syntax_matchesNull(v___x_920_, v___x_679_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_x_827_);
lean_dec(v___x_680_);
v___x_922_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_923_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_924_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = l_Lean_Syntax_getArg(v___x_680_, v___x_926_);
v___x_928_ = l_Lean_Syntax_isNone(v___x_927_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; 
lean_inc(v___x_927_);
v___x_929_ = l_Lean_Syntax_matchesNull(v___x_927_, v___x_919_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v___x_927_);
lean_dec(v_x_827_);
lean_dec(v___x_680_);
v___x_930_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_931_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_932_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_934_ = l_Lean_Syntax_getArg(v___x_927_, v___x_679_);
lean_dec(v___x_927_);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_934_);
v___x_936_ = l_Lean_Syntax_isOfKind(v___x_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___x_934_);
lean_dec(v_x_827_);
lean_dec(v___x_680_);
v___x_937_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_938_ = l_Lean_MessageData_ofSyntax(v_decl_665_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_939_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_940_;
}
else
{
lean_object* v_xType_x3f_941_; lean_object* v___x_942_; 
lean_dec(v_decl_665_);
v_xType_x3f_941_ = l_Lean_Syntax_getArg(v___x_934_, v___x_919_);
lean_dec(v___x_934_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_xType_x3f_941_);
v_xType_x3f_885_ = v___x_942_;
v___y_886_ = v_a_666_;
v___y_887_ = v_a_667_;
v___y_888_ = v_a_668_;
v___y_889_ = v_a_669_;
v___y_890_ = v_a_670_;
v___y_891_ = v_a_671_;
goto v___jp_884_;
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v___x_927_);
lean_dec(v_decl_665_);
v___x_943_ = lean_box(0);
v_xType_x3f_885_ = v___x_943_;
v___y_886_ = v_a_666_;
v___y_887_ = v_a_667_;
v___y_888_ = v_a_668_;
v___y_889_ = v_a_669_;
v___y_890_ = v_a_670_;
v___y_891_ = v_a_671_;
goto v___jp_884_;
}
}
}
v___jp_828_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_box(0);
lean_inc(v_x_827_);
v___x_838_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_827_, v_a_836_, v___x_674_, v___x_674_, v___x_837_, v___y_835_, v___y_834_, v___y_832_, v___y_831_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref_known(v___x_838_, 1);
v___x_839_ = l_Lean_TSyntax_getId(v_x_827_);
v___x_840_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_839_, v___y_832_, v___y_831_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = l_Lean_LocalDecl_type(v_a_841_);
lean_dec(v_a_841_);
v___x_843_ = l_Lean_Elab_Term_exprToSyntax(v___x_842_, v___y_835_, v___y_834_, v___y_832_, v___y_831_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_867_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_867_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_867_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_867_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_ref_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v_ref_848_ = lean_ctor_get(v___y_829_, 5);
v___x_849_ = 0;
v___x_850_ = l_Lean_SourceInfo_fromRef(v_ref_848_, v___x_849_);
lean_inc_n(v___x_850_, 7);
v___x_851_ = l_Lean_Syntax_node1(v___x_850_, v___x_821_, v_x_827_);
v___x_852_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_853_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_854_, 0, v___x_850_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_856_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_850_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_Syntax_node2(v___x_850_, v___x_855_, v___x_857_, v_a_844_);
v___x_859_ = l_Lean_Syntax_node1(v___x_850_, v___x_852_, v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_850_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_Syntax_node5(v___x_850_, v___x_681_, v___x_851_, v___x_854_, v___x_859_, v___x_861_, v___y_833_);
v___x_863_ = l_Lean_Syntax_node1(v___x_850_, v___x_673_, v___x_862_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_863_);
v___x_865_ = v___x_846_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_dec(v___y_833_);
lean_dec(v_x_827_);
return v___x_843_;
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v___y_833_);
lean_dec(v_x_827_);
v_a_868_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_840_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_840_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v___y_833_);
lean_dec(v_x_827_);
v_a_876_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_838_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_838_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(4u);
v___x_893_ = l_Lean_Syntax_getArg(v___x_680_, v___x_892_);
lean_dec(v___x_680_);
if (lean_obj_tag(v_xType_x3f_885_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
v___y_829_ = v___y_890_;
v___y_830_ = v___y_891_;
v___y_831_ = v___y_889_;
v___y_832_ = v___y_888_;
v___y_833_ = v___x_893_;
v___y_834_ = v___y_887_;
v___y_835_ = v___y_886_;
v_a_836_ = v___x_894_;
goto v___jp_828_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_912_; 
v_val_895_ = lean_ctor_get(v_xType_x3f_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v_xType_x3f_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_897_ = v_xType_x3f_885_;
v_isShared_898_ = v_isSharedCheck_912_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v_xType_x3f_885_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_912_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Elab_Term_elabType(v_val_895_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
v___y_829_ = v___y_890_;
v___y_830_ = v___y_891_;
v___y_831_ = v___y_889_;
v___y_832_ = v___y_888_;
v___y_833_ = v___x_893_;
v___y_834_ = v___y_887_;
v___y_835_ = v___y_886_;
v_a_836_ = v___x_902_;
goto v___jp_828_;
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_897_);
lean_dec(v___x_893_);
lean_dec(v_x_827_);
v_a_904_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_899_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
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
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_decl_665_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_945_, lean_object* v_decl_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_945_, v_decl_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_letOrReassign_945_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_955_, lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_965_, v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(lean_object* v_msgData_975_, lean_object* v_macroStack_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___redArg(v_msgData_975_, v_macroStack_976_, v___y_981_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1___boxed(lean_object* v_msgData_985_, lean_object* v_macroStack_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__1(v_msgData_985_, v_macroStack_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(lean_object* v_msg_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_ref_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_ref_1001_ = lean_ctor_get(v___y_998_, 5);
v___x_1002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_inc(v_ref_1001_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_ref_1001_);
lean_ctor_set(v___x_1007_, 1, v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg___boxed(lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1018_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__0));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__2));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_postponeValue_1034_; uint8_t v_generalize_1035_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; 
v_postponeValue_1034_ = lean_ctor_get_uint8(v_config_1025_, sizeof(void*)*1 + 3);
v_generalize_1035_ = lean_ctor_get_uint8(v_config_1025_, sizeof(void*)*1 + 4);
if (v_postponeValue_1034_ == 0)
{
v___y_1037_ = v_a_1026_;
v___y_1038_ = v_a_1027_;
v___y_1039_ = v_a_1028_;
v___y_1040_ = v_a_1029_;
v___y_1041_ = v_a_1030_;
v___y_1042_ = v_a_1031_;
v___y_1043_ = v_a_1032_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__3);
v___x_1049_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1048_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1049_;
}
v___jp_1036_:
{
if (v_generalize_1035_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___closed__1);
v___x_1047_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_1046_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec_ref(v_config_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(lean_object* v_00_u03b1_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_1061_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0(v_00_u03b1_1071_, v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg(){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___closed__0);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg___boxed(lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(lean_object* v_00_u03b1_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_00_u03b1_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_00_u03b1_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(lean_object* v_lctx_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_keyedConfig_1119_; uint8_t v_trackZetaDelta_1120_; lean_object* v_zetaDeltaSet_1121_; lean_object* v_localInstances_1122_; lean_object* v_defEqCtx_x3f_1123_; lean_object* v_synthPendingDepth_1124_; lean_object* v_canUnfold_x3f_1125_; uint8_t v_univApprox_1126_; uint8_t v_inTypeClassResolution_1127_; uint8_t v_cacheInferType_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_keyedConfig_1119_ = lean_ctor_get(v___y_1114_, 0);
v_trackZetaDelta_1120_ = lean_ctor_get_uint8(v___y_1114_, sizeof(void*)*7);
v_zetaDeltaSet_1121_ = lean_ctor_get(v___y_1114_, 1);
v_localInstances_1122_ = lean_ctor_get(v___y_1114_, 3);
v_defEqCtx_x3f_1123_ = lean_ctor_get(v___y_1114_, 4);
v_synthPendingDepth_1124_ = lean_ctor_get(v___y_1114_, 5);
v_canUnfold_x3f_1125_ = lean_ctor_get(v___y_1114_, 6);
v_univApprox_1126_ = lean_ctor_get_uint8(v___y_1114_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1127_ = lean_ctor_get_uint8(v___y_1114_, sizeof(void*)*7 + 2);
v_cacheInferType_1128_ = lean_ctor_get_uint8(v___y_1114_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1125_);
lean_inc(v_synthPendingDepth_1124_);
lean_inc(v_defEqCtx_x3f_1123_);
lean_inc_ref(v_localInstances_1122_);
lean_inc(v_zetaDeltaSet_1121_);
lean_inc_ref(v_keyedConfig_1119_);
v___x_1129_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1129_, 0, v_keyedConfig_1119_);
lean_ctor_set(v___x_1129_, 1, v_zetaDeltaSet_1121_);
lean_ctor_set(v___x_1129_, 2, v_lctx_1110_);
lean_ctor_set(v___x_1129_, 3, v_localInstances_1122_);
lean_ctor_set(v___x_1129_, 4, v_defEqCtx_x3f_1123_);
lean_ctor_set(v___x_1129_, 5, v_synthPendingDepth_1124_);
lean_ctor_set(v___x_1129_, 6, v_canUnfold_x3f_1125_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7, v_trackZetaDelta_1120_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7 + 1, v_univApprox_1126_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7 + 3, v_cacheInferType_1128_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
v___x_1130_ = lean_apply_7(v_x_1111_, v___y_1112_, v___y_1113_, v___x_1129_, v___y_1115_, v___y_1116_, v___y_1117_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg___boxed(lean_object* v_lctx_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1139_, v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_00_u03b1_1149_, lean_object* v_lctx_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___redArg(v_lctx_1150_, v_x_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_lctx_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_00_u03b1_1160_, v_lctx_1161_, v_x_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(lean_object* v_k_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed(lean_object* v_k_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0(v_k_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_name_1193_, lean_object* v_type_1194_, lean_object* v_val_1195_, lean_object* v_k_1196_, uint8_t v_nondep_1197_, uint8_t v_kind_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc_ref(v___y_1199_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___lam__0___boxed), 10, 4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_name_1217_, lean_object* v_type_1218_, lean_object* v_val_1219_, lean_object* v_k_1220_, lean_object* v_nondep_1221_, lean_object* v_kind_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_nondep_boxed_1231_; uint8_t v_kind_boxed_1232_; lean_object* v_res_1233_; 
v_nondep_boxed_1231_ = lean_unbox(v_nondep_1221_);
v_kind_boxed_1232_ = lean_unbox(v_kind_1222_);
v_res_1233_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1217_, v_type_1218_, v_val_1219_, v_k_1220_, v_nondep_boxed_1231_, v_kind_boxed_1232_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_00_u03b1_1234_, lean_object* v_name_1235_, lean_object* v_type_1236_, lean_object* v_val_1237_, lean_object* v_k_1238_, uint8_t v_nondep_1239_, uint8_t v_kind_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_name_1235_, v_type_1236_, v_val_1237_, v_k_1238_, v_nondep_1239_, v_kind_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_name_1251_, lean_object* v_type_1252_, lean_object* v_val_1253_, lean_object* v_k_1254_, lean_object* v_nondep_1255_, lean_object* v_kind_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v_nondep_boxed_1265_; uint8_t v_kind_boxed_1266_; lean_object* v_res_1267_; 
v_nondep_boxed_1265_ = lean_unbox(v_nondep_1255_);
v_kind_boxed_1266_ = lean_unbox(v_kind_1256_);
v_res_1267_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_00_u03b1_1250_, v_name_1251_, v_type_1252_, v_val_1253_, v_k_1254_, v_nondep_boxed_1265_, v_kind_boxed_1266_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
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
lean_dec_ref_known(v___x_1281_, 1);
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
uint8_t v___x_98701__boxed_1298_; uint8_t v___x_98704__boxed_1299_; lean_object* v_res_1300_; 
v___x_98701__boxed_1298_ = lean_unbox(v___x_1287_);
v___x_98704__boxed_1299_ = lean_unbox(v___x_1290_);
v_res_1300_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1285_, v___x_1286_, v___x_98701__boxed_1298_, v___x_1288_, v___x_1289_, v___x_98704__boxed_1299_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(lean_object* v_n_1331_, lean_object* v_k_1332_, lean_object* v_v_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_n_1331_, v___x_1334_, v_k_1332_, v_v_1333_);
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
v_newNode_1401_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v___x_1400_, v_x_1346_, v_x_1347_);
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
v___x_1408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_x_1345_, v_ks_1404_, v_vs_1405_, v___x_1406_, v___x_1407_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(size_t v_depth_1416_, lean_object* v_keys_1417_, lean_object* v_vals_1418_, lean_object* v_i_1419_, lean_object* v_entries_1420_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_depth_1436_, lean_object* v_keys_1437_, lean_object* v_vals_1438_, lean_object* v_i_1439_, lean_object* v_entries_1440_){
_start:
{
size_t v_depth_boxed_1441_; lean_object* v_res_1442_; 
v_depth_boxed_1441_ = lean_unbox_usize(v_depth_1436_);
lean_dec(v_depth_1436_);
v_res_1442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_boxed_1441_, v_keys_1437_, v_vals_1438_, v_i_1439_, v_entries_1440_);
lean_dec_ref(v_vals_1438_);
lean_dec_ref(v_keys_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
size_t v_x_98836__boxed_1448_; size_t v_x_98837__boxed_1449_; lean_object* v_res_1450_; 
v_x_98836__boxed_1448_ = lean_unbox_usize(v_x_1444_);
lean_dec(v_x_1444_);
v_x_98837__boxed_1449_ = lean_unbox_usize(v_x_1445_);
lean_dec(v_x_1445_);
v_res_1450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1443_, v_x_98836__boxed_1448_, v_x_98837__boxed_1449_, v_x_1446_, v_x_1447_);
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
lean_dec_ref_known(v___x_1556_, 1);
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
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = 1;
v___x_1571_ = l_Lean_Meta_mkForallFVars(v___x_1560_, v_a_1557_, v___x_1543_, v___x_1542_, v___x_1542_, v___x_1570_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
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
lean_inc_ref(v___y_1598_);
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
lean_dec_ref_known(v___x_1604_, 1);
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
lean_dec_ref_known(v___x_1609_, 1);
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
uint8_t v___x_99155__boxed_1658_; uint8_t v___x_99156__boxed_1659_; uint8_t v___y_99158__boxed_1660_; lean_object* v_res_1661_; 
v___x_99155__boxed_1658_ = lean_unbox(v___x_1646_);
v___x_99156__boxed_1659_ = lean_unbox(v___x_1647_);
v___y_99158__boxed_1660_ = lean_unbox(v___y_1649_);
v_res_1661_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1644_, v_value_1645_, v___x_99155__boxed_1658_, v___x_99156__boxed_1659_, v___x_1648_, v___y_99158__boxed_1660_, v_xs_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___x_1648_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1662_, lean_object* v_a_1663_, uint8_t v_zeta_1664_, uint8_t v___y_1665_, lean_object* v_x_1666_, uint8_t v_usedOnly_1667_, uint8_t v___x_1668_, uint8_t v___x_1669_, lean_object* v_snd_1670_, lean_object* v_h_x27_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
lean_inc_ref(v_h_x27_1671_);
v___x_1680_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1662_, v_h_x27_1671_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1680_, 1);
v___x_1681_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1663_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1681_) == 0)
{
if (v_zeta_1664_ == 0)
{
if (v___y_1665_ == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref(v_snd_1670_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = lean_unsigned_to_nat(2u);
v___x_1684_ = lean_mk_empty_array_with_capacity(v___x_1683_);
v___x_1685_ = lean_array_push(v___x_1684_, v_x_1666_);
v___x_1686_ = lean_array_push(v___x_1685_, v_h_x27_1671_);
v___x_1687_ = 1;
v___x_1688_ = l_Lean_Meta_mkLetFVars(v___x_1686_, v_a_1682_, v_usedOnly_1667_, v___x_1668_, v___x_1687_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec_ref(v___x_1686_);
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; 
v_a_1689_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1690_ = lean_unsigned_to_nat(2u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = lean_array_push(v___x_1691_, v_x_1666_);
v___x_1693_ = lean_array_push(v___x_1692_, v_h_x27_1671_);
v___x_1694_ = 1;
v___x_1695_ = l_Lean_Meta_mkLambdaFVars(v___x_1693_, v_a_1689_, v___x_1668_, v___x_1669_, v___x_1668_, v___x_1669_, v___x_1694_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec_ref(v___x_1693_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
lean_inc_ref(v_snd_1670_);
v___x_1697_ = l_Lean_Meta_mkEqRefl(v_snd_1670_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_mkAppB(v_a_1696_, v_snd_1670_, v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_dec(v_a_1696_);
lean_dec_ref(v_snd_1670_);
return v___x_1697_;
}
}
else
{
lean_dec_ref(v_snd_1670_);
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1707_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = lean_mk_empty_array_with_capacity(v___x_1708_);
lean_inc_ref(v___x_1709_);
v___x_1710_ = lean_array_push(v___x_1709_, v_x_1666_);
v___x_1711_ = lean_array_push(v___x_1710_, v_h_x27_1671_);
v___x_1712_ = l_Lean_Expr_abstractM(v_a_1707_, v___x_1711_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec_ref(v___x_1711_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
lean_inc_ref(v_snd_1670_);
v___x_1714_ = l_Lean_Meta_mkEqRefl(v_snd_1670_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1719_ = lean_array_push(v___x_1709_, v_snd_1670_);
v___x_1720_ = lean_array_push(v___x_1719_, v_a_1715_);
v___x_1721_ = lean_expr_instantiate_rev(v_a_1713_, v___x_1720_);
lean_dec_ref(v___x_1720_);
lean_dec(v_a_1713_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1721_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_dec(v_a_1713_);
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_snd_1670_);
return v___x_1714_;
}
}
else
{
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_snd_1670_);
return v___x_1712_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1671_);
lean_dec_ref(v_snd_1670_);
lean_dec_ref(v_x_1666_);
return v___x_1681_;
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v_h_x27_1671_);
lean_dec_ref(v_snd_1670_);
lean_dec_ref(v_x_1666_);
lean_dec_ref(v_a_1663_);
v_a_1726_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1680_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1680_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_1734_ = _args[0];
lean_object* v_a_1735_ = _args[1];
lean_object* v_zeta_1736_ = _args[2];
lean_object* v___y_1737_ = _args[3];
lean_object* v_x_1738_ = _args[4];
lean_object* v_usedOnly_1739_ = _args[5];
lean_object* v___x_1740_ = _args[6];
lean_object* v___x_1741_ = _args[7];
lean_object* v_snd_1742_ = _args[8];
lean_object* v_h_x27_1743_ = _args[9];
lean_object* v___y_1744_ = _args[10];
lean_object* v___y_1745_ = _args[11];
lean_object* v___y_1746_ = _args[12];
lean_object* v___y_1747_ = _args[13];
lean_object* v___y_1748_ = _args[14];
lean_object* v___y_1749_ = _args[15];
lean_object* v___y_1750_ = _args[16];
lean_object* v___y_1751_ = _args[17];
_start:
{
uint8_t v_zeta_boxed_1752_; uint8_t v___y_99382__boxed_1753_; uint8_t v_usedOnly_boxed_1754_; uint8_t v___x_99383__boxed_1755_; uint8_t v___x_99384__boxed_1756_; lean_object* v_res_1757_; 
v_zeta_boxed_1752_ = lean_unbox(v_zeta_1736_);
v___y_99382__boxed_1753_ = lean_unbox(v___y_1737_);
v_usedOnly_boxed_1754_ = lean_unbox(v_usedOnly_1739_);
v___x_99383__boxed_1755_ = lean_unbox(v___x_1740_);
v___x_99384__boxed_1756_ = lean_unbox(v___x_1741_);
v_res_1757_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_1734_, v_a_1735_, v_zeta_boxed_1752_, v___y_99382__boxed_1753_, v_x_1738_, v_usedOnly_boxed_1754_, v___x_99383__boxed_1755_, v___x_99384__boxed_1756_, v_snd_1742_, v_h_x27_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_eq_x3f_1758_, lean_object* v_a_1759_, uint8_t v_zeta_1760_, lean_object* v_x_1761_, uint8_t v_usedOnly_1762_, uint8_t v___x_1763_, lean_object* v_snd_1764_, uint8_t v___y_1765_, uint8_t v___x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
if (lean_obj_tag(v_eq_x3f_1758_) == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_1759_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1775_) == 0)
{
if (v_zeta_1760_ == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; 
lean_dec_ref(v_snd_1764_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
v___x_1779_ = lean_array_push(v___x_1778_, v_x_1761_);
v___x_1780_ = 1;
v___x_1781_ = l_Lean_Meta_mkLetFVars(v___x_1779_, v_a_1776_, v_usedOnly_1762_, v___x_1763_, v___x_1780_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec_ref(v___x_1779_);
return v___x_1781_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1782_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_mk_empty_array_with_capacity(v___x_1783_);
v___x_1785_ = lean_array_push(v___x_1784_, v_x_1761_);
v___x_1786_ = l_Lean_Expr_abstractM(v_a_1782_, v___x_1785_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec_ref(v___x_1785_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = lean_expr_instantiate1(v_a_1787_, v_snd_1764_);
lean_dec_ref(v_snd_1764_);
lean_dec(v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_dec_ref(v_snd_1764_);
return v___x_1786_;
}
}
}
else
{
lean_dec_ref(v_snd_1764_);
lean_dec_ref(v_x_1761_);
return v___x_1775_;
}
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1797_; 
v_val_1796_ = lean_ctor_get(v_eq_x3f_1758_, 0);
lean_inc(v_val_1796_);
lean_dec_ref_known(v_eq_x3f_1758_, 1);
lean_inc_ref(v_snd_1764_);
lean_inc_ref(v_x_1761_);
v___x_1797_ = l_Lean_Meta_mkEq(v_x_1761_, v_snd_1764_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
lean_inc_ref(v_x_1761_);
v___x_1799_ = l_Lean_Meta_mkEqRefl(v_x_1761_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_box(v_zeta_1760_);
v___x_1802_ = lean_box(v___y_1765_);
v___x_1803_ = lean_box(v_usedOnly_1762_);
v___x_1804_ = lean_box(v___x_1763_);
v___x_1805_ = lean_box(v___x_1766_);
lean_inc(v_val_1796_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1806_, 0, v_val_1796_);
lean_closure_set(v___f_1806_, 1, v_a_1759_);
lean_closure_set(v___f_1806_, 2, v___x_1801_);
lean_closure_set(v___f_1806_, 3, v___x_1802_);
lean_closure_set(v___f_1806_, 4, v_x_1761_);
lean_closure_set(v___f_1806_, 5, v___x_1803_);
lean_closure_set(v___f_1806_, 6, v___x_1804_);
lean_closure_set(v___f_1806_, 7, v___x_1805_);
lean_closure_set(v___f_1806_, 8, v_snd_1764_);
v___x_1807_ = l_Lean_TSyntax_getId(v_val_1796_);
lean_dec(v_val_1796_);
v___x_1808_ = 0;
v___x_1809_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_1807_, v_a_1798_, v_a_1800_, v___f_1806_, v___x_1766_, v___x_1808_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1809_;
}
else
{
lean_dec(v_a_1798_);
lean_dec(v_val_1796_);
lean_dec_ref(v_snd_1764_);
lean_dec_ref(v_x_1761_);
lean_dec_ref(v_a_1759_);
return v___x_1799_;
}
}
else
{
lean_dec(v_val_1796_);
lean_dec_ref(v_snd_1764_);
lean_dec_ref(v_x_1761_);
lean_dec_ref(v_a_1759_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_eq_x3f_1810_ = _args[0];
lean_object* v_a_1811_ = _args[1];
lean_object* v_zeta_1812_ = _args[2];
lean_object* v_x_1813_ = _args[3];
lean_object* v_usedOnly_1814_ = _args[4];
lean_object* v___x_1815_ = _args[5];
lean_object* v_snd_1816_ = _args[6];
lean_object* v___y_1817_ = _args[7];
lean_object* v___x_1818_ = _args[8];
lean_object* v___y_1819_ = _args[9];
lean_object* v___y_1820_ = _args[10];
lean_object* v___y_1821_ = _args[11];
lean_object* v___y_1822_ = _args[12];
lean_object* v___y_1823_ = _args[13];
lean_object* v___y_1824_ = _args[14];
lean_object* v___y_1825_ = _args[15];
lean_object* v___y_1826_ = _args[16];
_start:
{
uint8_t v_zeta_boxed_1827_; uint8_t v_usedOnly_boxed_1828_; uint8_t v___x_99537__boxed_1829_; uint8_t v___y_99539__boxed_1830_; uint8_t v___x_99540__boxed_1831_; lean_object* v_res_1832_; 
v_zeta_boxed_1827_ = lean_unbox(v_zeta_1812_);
v_usedOnly_boxed_1828_ = lean_unbox(v_usedOnly_1814_);
v___x_99537__boxed_1829_ = lean_unbox(v___x_1815_);
v___y_99539__boxed_1830_ = lean_unbox(v___y_1817_);
v___x_99540__boxed_1831_ = lean_unbox(v___x_1818_);
v_res_1832_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_eq_x3f_1810_, v_a_1811_, v_zeta_boxed_1827_, v_x_1813_, v_usedOnly_boxed_1828_, v___x_99537__boxed_1829_, v_snd_1816_, v___y_99539__boxed_1830_, v___x_99540__boxed_1831_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(lean_object* v_id_1833_, lean_object* v_eq_x3f_1834_, lean_object* v_a_1835_, uint8_t v_zeta_1836_, uint8_t v_usedOnly_1837_, uint8_t v___x_1838_, lean_object* v_snd_1839_, uint8_t v___y_1840_, uint8_t v___x_1841_, lean_object* v_letOrReassign_1842_, lean_object* v_a_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
lean_inc_ref(v_x_1844_);
v___x_1853_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_1833_, v_x_1844_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___y_1859_; lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1853_, 1);
v___x_1854_ = lean_box(v_zeta_1836_);
v___x_1855_ = lean_box(v_usedOnly_1837_);
v___x_1856_ = lean_box(v___x_1838_);
v___x_1857_ = lean_box(v___y_1840_);
v___x_1858_ = lean_box(v___x_1841_);
v___y_1859_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 17, 9);
lean_closure_set(v___y_1859_, 0, v_eq_x3f_1834_);
lean_closure_set(v___y_1859_, 1, v_a_1835_);
lean_closure_set(v___y_1859_, 2, v___x_1854_);
lean_closure_set(v___y_1859_, 3, v_x_1844_);
lean_closure_set(v___y_1859_, 4, v___x_1855_);
lean_closure_set(v___y_1859_, 5, v___x_1856_);
lean_closure_set(v___y_1859_, 6, v_snd_1839_);
lean_closure_set(v___y_1859_, 7, v___x_1857_);
lean_closure_set(v___y_1859_, 8, v___x_1858_);
v___x_1860_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1842_, v_a_1843_, v___y_1859_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
return v___x_1860_;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_x_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_letOrReassign_1842_);
lean_dec_ref(v_snd_1839_);
lean_dec_ref(v_a_1835_);
lean_dec(v_eq_x3f_1834_);
v_a_1861_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1853_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1853_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object** _args){
lean_object* v_id_1869_ = _args[0];
lean_object* v_eq_x3f_1870_ = _args[1];
lean_object* v_a_1871_ = _args[2];
lean_object* v_zeta_1872_ = _args[3];
lean_object* v_usedOnly_1873_ = _args[4];
lean_object* v___x_1874_ = _args[5];
lean_object* v_snd_1875_ = _args[6];
lean_object* v___y_1876_ = _args[7];
lean_object* v___x_1877_ = _args[8];
lean_object* v_letOrReassign_1878_ = _args[9];
lean_object* v_a_1879_ = _args[10];
lean_object* v_x_1880_ = _args[11];
lean_object* v___y_1881_ = _args[12];
lean_object* v___y_1882_ = _args[13];
lean_object* v___y_1883_ = _args[14];
lean_object* v___y_1884_ = _args[15];
lean_object* v___y_1885_ = _args[16];
lean_object* v___y_1886_ = _args[17];
lean_object* v___y_1887_ = _args[18];
lean_object* v___y_1888_ = _args[19];
_start:
{
uint8_t v_zeta_boxed_1889_; uint8_t v_usedOnly_boxed_1890_; uint8_t v___x_99650__boxed_1891_; uint8_t v___y_99652__boxed_1892_; uint8_t v___x_99653__boxed_1893_; lean_object* v_res_1894_; 
v_zeta_boxed_1889_ = lean_unbox(v_zeta_1872_);
v_usedOnly_boxed_1890_ = lean_unbox(v_usedOnly_1873_);
v___x_99650__boxed_1891_ = lean_unbox(v___x_1874_);
v___y_99652__boxed_1892_ = lean_unbox(v___y_1876_);
v___x_99653__boxed_1893_ = lean_unbox(v___x_1877_);
v_res_1894_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v_id_1869_, v_eq_x3f_1870_, v_a_1871_, v_zeta_boxed_1889_, v_usedOnly_boxed_1890_, v___x_99650__boxed_1891_, v_snd_1875_, v___y_99652__boxed_1892_, v___x_99653__boxed_1893_, v_letOrReassign_1878_, v_a_1879_, v_x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(uint8_t v___x_1895_, lean_object* v_____do__lift_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1896_, v___x_1895_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v___x_1907_, lean_object* v_____do__lift_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v___x_99724__boxed_1917_; lean_object* v_res_1918_; 
v___x_99724__boxed_1917_ = lean_unbox(v___x_1907_);
v_res_1918_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v___x_99724__boxed_1917_, v_____do__lift_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v_____do__lift_1908_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_term_1919_, lean_object* v___x_1920_, uint8_t v___x_1921_, lean_object* v___x_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_1919_, v___x_1920_, v___x_1921_, v___x_1921_, v___x_1922_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object* v_term_1932_, lean_object* v___x_1933_, lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_99759__boxed_1944_; lean_object* v_res_1945_; 
v___x_99759__boxed_1944_ = lean_unbox(v___x_1934_);
v_res_1945_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_term_1932_, v___x_1933_, v___x_99759__boxed_1944_, v___x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
lean_inc_ref(v___y_1947_);
v___x_1955_ = lean_apply_8(v_x_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_x_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec_ref(v___y_1957_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(lean_object* v___y_1966_, lean_object* v_mkInfoTree_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v_a_1973_, lean_object* v_a_x3f_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v_infoState_1977_; lean_object* v_trees_1978_; lean_object* v___x_1979_; 
v___x_1976_ = lean_st_ref_get(v___y_1966_);
v_infoState_1977_ = lean_ctor_get(v___x_1976_, 7);
lean_inc_ref(v_infoState_1977_);
lean_dec(v___x_1976_);
v_trees_1978_ = lean_ctor_get(v_infoState_1977_, 2);
lean_inc_ref(v_trees_1978_);
lean_dec_ref(v_infoState_1977_);
lean_inc(v___y_1966_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
v___x_1979_ = lean_apply_8(v_mkInfoTree_1967_, v_trees_1978_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1966_, lean_box(0));
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2018_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2018_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2018_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v_infoState_1985_; lean_object* v_env_1986_; lean_object* v_nextMacroScope_1987_; lean_object* v_ngen_1988_; lean_object* v_auxDeclNGen_1989_; lean_object* v_traceState_1990_; lean_object* v_cache_1991_; lean_object* v_messages_1992_; lean_object* v_snapshotTasks_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2017_; 
v___x_1984_ = lean_st_ref_take(v___y_1966_);
v_infoState_1985_ = lean_ctor_get(v___x_1984_, 7);
v_env_1986_ = lean_ctor_get(v___x_1984_, 0);
v_nextMacroScope_1987_ = lean_ctor_get(v___x_1984_, 1);
v_ngen_1988_ = lean_ctor_get(v___x_1984_, 2);
v_auxDeclNGen_1989_ = lean_ctor_get(v___x_1984_, 3);
v_traceState_1990_ = lean_ctor_get(v___x_1984_, 4);
v_cache_1991_ = lean_ctor_get(v___x_1984_, 5);
v_messages_1992_ = lean_ctor_get(v___x_1984_, 6);
v_snapshotTasks_1993_ = lean_ctor_get(v___x_1984_, 8);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1995_ = v___x_1984_;
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_snapshotTasks_1993_);
lean_inc(v_infoState_1985_);
lean_inc(v_messages_1992_);
lean_inc(v_cache_1991_);
lean_inc(v_traceState_1990_);
lean_inc(v_auxDeclNGen_1989_);
lean_inc(v_ngen_1988_);
lean_inc(v_nextMacroScope_1987_);
lean_inc(v_env_1986_);
lean_dec(v___x_1984_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
uint8_t v_enabled_1997_; lean_object* v_assignment_1998_; lean_object* v_lazyAssignment_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2015_; 
v_enabled_1997_ = lean_ctor_get_uint8(v_infoState_1985_, sizeof(void*)*3);
v_assignment_1998_ = lean_ctor_get(v_infoState_1985_, 0);
v_lazyAssignment_1999_ = lean_ctor_get(v_infoState_1985_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_infoState_1985_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_infoState_1985_, 2);
lean_dec(v_unused_2016_);
v___x_2001_ = v_infoState_1985_;
v_isShared_2002_ = v_isSharedCheck_2015_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_lazyAssignment_1999_);
lean_inc(v_assignment_1998_);
lean_dec(v_infoState_1985_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2015_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = l_Lean_PersistentArray_push___redArg(v_a_1973_, v_a_1980_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 2, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_assignment_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_lazyAssignment_1999_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v___x_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*3, v_enabled_1997_);
v___x_2005_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 7, v___x_2005_);
v___x_2007_ = v___x_1995_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_env_1986_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_nextMacroScope_1987_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_ngen_1988_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_auxDeclNGen_1989_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_traceState_1990_);
lean_ctor_set(v_reuseFailAlloc_2013_, 5, v_cache_1991_);
lean_ctor_set(v_reuseFailAlloc_2013_, 6, v_messages_1992_);
lean_ctor_set(v_reuseFailAlloc_2013_, 7, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 8, v_snapshotTasks_1993_);
v___x_2007_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_st_ref_set(v___y_1966_, v___x_2007_);
v___x_2009_ = lean_box(0);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2009_);
v___x_2011_ = v___x_1982_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_a_1973_);
v_a_2019_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1979_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1979_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0___boxed(lean_object* v___y_2027_, lean_object* v_mkInfoTree_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v_a_2034_, lean_object* v_a_x3f_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2027_, v_mkInfoTree_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v_a_2034_, v_a_x3f_2035_);
lean_dec(v_a_x3f_2035_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2027_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v_infoState_2041_; lean_object* v_trees_2042_; lean_object* v___x_2043_; lean_object* v_infoState_2044_; lean_object* v_env_2045_; lean_object* v_nextMacroScope_2046_; lean_object* v_ngen_2047_; lean_object* v_auxDeclNGen_2048_; lean_object* v_traceState_2049_; lean_object* v_cache_2050_; lean_object* v_messages_2051_; lean_object* v_snapshotTasks_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2075_; 
v___x_2040_ = lean_st_ref_get(v___y_2038_);
v_infoState_2041_ = lean_ctor_get(v___x_2040_, 7);
lean_inc_ref(v_infoState_2041_);
lean_dec(v___x_2040_);
v_trees_2042_ = lean_ctor_get(v_infoState_2041_, 2);
lean_inc_ref(v_trees_2042_);
lean_dec_ref(v_infoState_2041_);
v___x_2043_ = lean_st_ref_take(v___y_2038_);
v_infoState_2044_ = lean_ctor_get(v___x_2043_, 7);
v_env_2045_ = lean_ctor_get(v___x_2043_, 0);
v_nextMacroScope_2046_ = lean_ctor_get(v___x_2043_, 1);
v_ngen_2047_ = lean_ctor_get(v___x_2043_, 2);
v_auxDeclNGen_2048_ = lean_ctor_get(v___x_2043_, 3);
v_traceState_2049_ = lean_ctor_get(v___x_2043_, 4);
v_cache_2050_ = lean_ctor_get(v___x_2043_, 5);
v_messages_2051_ = lean_ctor_get(v___x_2043_, 6);
v_snapshotTasks_2052_ = lean_ctor_get(v___x_2043_, 8);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2054_ = v___x_2043_;
v_isShared_2055_ = v_isSharedCheck_2075_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snapshotTasks_2052_);
lean_inc(v_infoState_2044_);
lean_inc(v_messages_2051_);
lean_inc(v_cache_2050_);
lean_inc(v_traceState_2049_);
lean_inc(v_auxDeclNGen_2048_);
lean_inc(v_ngen_2047_);
lean_inc(v_nextMacroScope_2046_);
lean_inc(v_env_2045_);
lean_dec(v___x_2043_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2075_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
uint8_t v_enabled_2056_; lean_object* v_assignment_2057_; lean_object* v_lazyAssignment_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2073_; 
v_enabled_2056_ = lean_ctor_get_uint8(v_infoState_2044_, sizeof(void*)*3);
v_assignment_2057_ = lean_ctor_get(v_infoState_2044_, 0);
v_lazyAssignment_2058_ = lean_ctor_get(v_infoState_2044_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_infoState_2044_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_infoState_2044_, 2);
lean_dec(v_unused_2074_);
v___x_2060_ = v_infoState_2044_;
v_isShared_2061_ = v_isSharedCheck_2073_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_lazyAssignment_2058_);
lean_inc(v_assignment_2057_);
lean_dec(v_infoState_2044_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2073_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2062_ = lean_unsigned_to_nat(32u);
v___x_2063_ = lean_mk_empty_array_with_capacity(v___x_2062_);
lean_dec_ref(v___x_2063_);
v___x_2064_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___closed__1);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 2, v___x_2064_);
v___x_2066_ = v___x_2060_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_assignment_2057_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_lazyAssignment_2058_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v___x_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2072_, sizeof(void*)*3, v_enabled_2056_);
v___x_2066_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 7, v___x_2066_);
v___x_2068_ = v___x_2054_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_env_2045_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_nextMacroScope_2046_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_ngen_2047_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_auxDeclNGen_2048_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_traceState_2049_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_cache_2050_);
lean_ctor_set(v_reuseFailAlloc_2071_, 6, v_messages_2051_);
lean_ctor_set(v_reuseFailAlloc_2071_, 7, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2071_, 8, v_snapshotTasks_2052_);
v___x_2068_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_st_ref_set(v___y_2038_, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_trees_2042_);
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg___boxed(lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2076_);
lean_dec(v___y_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(lean_object* v_x_2079_, lean_object* v_mkInfoTree_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v_infoState_2089_; uint8_t v_enabled_2090_; 
v___x_2088_ = lean_st_ref_get(v___y_2086_);
v_infoState_2089_ = lean_ctor_get(v___x_2088_, 7);
lean_inc_ref(v_infoState_2089_);
lean_dec(v___x_2088_);
v_enabled_2090_ = lean_ctor_get_uint8(v_infoState_2089_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2089_);
if (v_enabled_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v_mkInfoTree_2080_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
v___x_2091_ = lean_apply_7(v_x_2079_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v_a_2093_; lean_object* v_r_2094_; 
v___x_2092_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_2086_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
v_r_2094_ = lean_apply_7(v_x_2079_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
if (lean_obj_tag(v_r_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2119_; 
v_a_2095_ = lean_ctor_get(v_r_2094_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_r_2094_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2097_ = v_r_2094_;
v_isShared_2098_ = v_isSharedCheck_2119_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v_r_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2119_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
lean_inc(v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2086_, v_mkInfoTree_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v_a_2093_, v___x_2100_);
lean_dec_ref(v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2101_, 0);
lean_dec(v_unused_2109_);
v___x_2103_ = v___x_2101_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v___x_2101_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v_a_2095_);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2095_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_a_2095_);
v_a_2110_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2101_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2101_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v_r_2094_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v_r_2094_, 1);
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___lam__0(v___y_2086_, v_mkInfoTree_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v_a_2093_, v___x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2130_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 1);
lean_ctor_set(v___x_2124_, 0, v_a_2120_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2120_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_a_2120_);
v_a_2131_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2122_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2122_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg___boxed(lean_object* v_x_2139_, lean_object* v_mkInfoTree_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2139_, v_mkInfoTree_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(lean_object* v_stx_2149_, lean_object* v_output_2150_, lean_object* v_trees_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_lctx_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_lctx_2159_ = lean_ctor_get(v___y_2154_, 2);
lean_inc_ref(v_lctx_2159_);
v___x_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2160_, 0, v_lctx_2159_);
lean_ctor_set(v___x_2160_, 1, v_stx_2149_);
lean_ctor_set(v___x_2160_, 2, v_output_2150_);
v___x_2161_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v_trees_2151_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_stx_2164_, lean_object* v_output_2165_, lean_object* v_trees_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0(v_stx_2164_, v_output_2165_, v_trees_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(lean_object* v_stx_2175_, lean_object* v_output_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___f_2185_; lean_object* v___x_2186_; 
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2185_, 0, v_stx_2175_);
lean_closure_set(v___f_2185_, 1, v_output_2176_);
v___x_2186_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_2177_, v___f_2185_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg___boxed(lean_object* v_stx_2187_, lean_object* v_output_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_2187_, v_output_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_beforeStx_2198_, lean_object* v_afterStx_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_inc_ref(v___y_2201_);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2209_, 0, v_x_2200_);
lean_closure_set(v___f_2209_, 1, v___y_2201_);
lean_inc(v_afterStx_2199_);
lean_inc(v_beforeStx_2198_);
v___x_2210_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2210_, 0, lean_box(0));
lean_closure_set(v___x_2210_, 1, v_beforeStx_2198_);
lean_closure_set(v___x_2210_, 2, v_afterStx_2199_);
lean_closure_set(v___x_2210_, 3, v___f_2209_);
v___x_2211_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_beforeStx_2198_, v_afterStx_2199_, v___x_2210_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2211_) == 0)
{
return v___x_2211_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_beforeStx_2220_, lean_object* v_afterStx_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_2220_, v_afterStx_2221_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2231_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__1));
v___x_2235_ = l_String_toRawSubstring_x27(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(lean_object* v_rhs_2257_, uint8_t v___x_2258_, lean_object* v_config_2259_, lean_object* v_a_2260_, uint8_t v___x_2261_, lean_object* v___x_2262_, lean_object* v___x_2263_, lean_object* v___x_2264_, lean_object* v___f_2265_, lean_object* v___x_2266_, lean_object* v_body_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_term_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v_ref_2284_; lean_object* v___y_2285_; lean_object* v_ref_2291_; lean_object* v_quotContext_2292_; lean_object* v_currMacroScope_2293_; lean_object* v_ref_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_eq_x3f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_ref_2291_ = lean_ctor_get(v___y_2273_, 5);
v_quotContext_2292_ = lean_ctor_get(v___y_2273_, 10);
v_currMacroScope_2293_ = lean_ctor_get(v___y_2273_, 11);
v_ref_2294_ = l_Lean_replaceRef(v_rhs_2257_, v_ref_2291_);
v___x_2295_ = l_Lean_SourceInfo_fromRef(v_ref_2294_, v___x_2258_);
lean_dec(v_ref_2294_);
v___x_2296_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__0));
lean_inc_n(v___x_2295_, 2);
v___x_2297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__2);
v_eq_x3f_2299_ = lean_ctor_get(v_config_2259_, 0);
lean_inc(v_eq_x3f_2299_);
lean_dec_ref(v_config_2259_);
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__3));
lean_inc(v_currMacroScope_2293_);
lean_inc(v_quotContext_2292_);
v___x_2301_ = l_Lean_addMacroScope(v_quotContext_2292_, v___x_2300_, v_currMacroScope_2293_);
v___x_2302_ = lean_box(0);
lean_inc(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2295_);
lean_ctor_set(v___x_2303_, 1, v___x_2298_);
lean_ctor_set(v___x_2303_, 2, v___x_2301_);
lean_ctor_set(v___x_2303_, 3, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__4));
lean_inc_ref(v___x_2264_);
lean_inc_ref(v___x_2263_);
lean_inc_ref(v___x_2262_);
v___x_2305_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_node2(v___x_2295_, v___x_2305_, v___x_2297_, v___x_2303_);
if (lean_obj_tag(v_eq_x3f_2299_) == 1)
{
lean_object* v_val_2307_; lean_object* v___x_2308_; 
v_val_2307_ = lean_ctor_get(v_eq_x3f_2299_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v_eq_x3f_2299_, 1);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v_ref_2291_);
v___x_2308_ = lean_apply_9(v___f_2265_, v_ref_2291_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, lean_box(0));
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_n(v_a_2309_, 23);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2264_, 5);
lean_inc_ref_n(v___x_2263_, 5);
lean_inc_ref_n(v___x_2262_, 5);
v___x_2311_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2313_, 0, v_a_2309_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2314_, 0, v_a_2309_);
lean_ctor_set(v___x_2314_, 1, v___x_2296_);
v___x_2315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2309_);
lean_ctor_set(v___x_2315_, 1, v___x_2298_);
lean_ctor_set(v___x_2315_, 2, v___x_2301_);
lean_ctor_set(v___x_2315_, 3, v___x_2302_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_a_2309_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_a_2309_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2321_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2309_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2325_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_a_2309_);
lean_ctor_set(v___x_2326_, 1, v___x_2324_);
v___x_2327_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2328_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2309_);
lean_ctor_set(v___x_2329_, 1, v___x_2327_);
lean_ctor_set(v___x_2329_, 2, v___x_2328_);
v___x_2330_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2331_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2330_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2309_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = l_Lean_Syntax_node2(v_a_2309_, v___x_2327_, v_val_2307_, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node2(v_a_2309_, v___x_2331_, v___x_2334_, v___x_2306_);
v___x_2336_ = l_Lean_Syntax_node1(v_a_2309_, v___x_2327_, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_a_2309_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2340_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2342_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2309_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_Syntax_node1(v_a_2309_, v___x_2327_, v___x_2266_);
v___x_2346_ = l_Lean_Syntax_node1(v_a_2309_, v___x_2327_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_a_2309_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_Syntax_node4(v_a_2309_, v___x_2342_, v___x_2344_, v___x_2346_, v___x_2348_, v_body_2267_);
v___x_2350_ = l_Lean_Syntax_node1(v_a_2309_, v___x_2327_, v___x_2349_);
v___x_2351_ = l_Lean_Syntax_node1(v_a_2309_, v___x_2340_, v___x_2350_);
lean_inc_ref(v___x_2329_);
v___x_2352_ = l_Lean_Syntax_node6(v_a_2309_, v___x_2325_, v___x_2326_, v___x_2329_, v___x_2329_, v___x_2336_, v___x_2338_, v___x_2351_);
lean_inc_ref(v___x_2319_);
lean_inc_ref(v___x_2315_);
lean_inc_ref(v___x_2314_);
v___x_2353_ = l_Lean_Syntax_node5(v_a_2309_, v___x_2321_, v___x_2323_, v___x_2314_, v___x_2315_, v___x_2319_, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node7(v_a_2309_, v___x_2311_, v___x_2313_, v___x_2314_, v___x_2315_, v___x_2317_, v_rhs_2257_, v___x_2319_, v___x_2353_);
lean_inc(v_ref_2291_);
v_term_2277_ = v___x_2354_;
v___y_2278_ = v___y_2268_;
v___y_2279_ = v___y_2269_;
v___y_2280_ = v___y_2270_;
v___y_2281_ = v___y_2271_;
v___y_2282_ = v___y_2272_;
v___y_2283_ = v___y_2273_;
v_ref_2284_ = v_ref_2291_;
v___y_2285_ = v___y_2274_;
goto v___jp_2276_;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_val_2307_);
lean_dec(v___x_2306_);
lean_dec(v___x_2301_);
lean_dec(v_body_2267_);
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec_ref(v_a_2260_);
lean_dec(v_rhs_2257_);
v_a_2355_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2308_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2308_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v___x_2363_; 
lean_dec(v_eq_x3f_2299_);
lean_inc_ref(v_a_2260_);
v___x_2363_ = l_Lean_Elab_Term_exprToSyntax(v_a_2260_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v_ref_2291_);
v___x_2365_ = lean_apply_9(v___f_2265_, v_ref_2291_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, lean_box(0));
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_n(v_a_2366_, 32);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__5));
lean_inc_ref_n(v___x_2264_, 8);
lean_inc_ref_n(v___x_2263_, 8);
lean_inc_ref_n(v___x_2262_, 8);
v___x_2368_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__6));
v___x_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_a_2366_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2366_);
lean_ctor_set(v___x_2371_, 1, v___x_2296_);
v___x_2372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2372_, 0, v_a_2366_);
lean_ctor_set(v___x_2372_, 1, v___x_2298_);
lean_ctor_set(v___x_2372_, 2, v___x_2301_);
lean_ctor_set(v___x_2372_, 3, v___x_2302_);
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_a_2366_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_2376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_a_2366_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__8));
v___x_2378_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__9));
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_a_2366_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_2382_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2366_);
lean_ctor_set(v___x_2383_, 1, v___x_2381_);
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2385_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2386_, 0, v_a_2366_);
lean_ctor_set(v___x_2386_, 1, v___x_2384_);
lean_ctor_set(v___x_2386_, 2, v___x_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__17));
v___x_2388_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_a_2366_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_a_2366_);
lean_ctor_set(v___x_2391_, 1, v___x_2387_);
v___x_2392_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__18));
v___x_2393_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__19));
v___x_2395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_a_2366_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__20));
v___x_2397_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_2399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_a_2366_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2397_, v___x_2399_);
v___x_2401_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2400_);
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__22));
v___x_2403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2403_, 0, v_a_2366_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
lean_inc_ref_n(v___x_2386_, 2);
v___x_2404_ = l_Lean_Syntax_node5(v_a_2366_, v___x_2393_, v___x_2395_, v___x_2401_, v___x_2386_, v___x_2403_, v_a_2364_);
v___x_2405_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_a_2366_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
lean_inc_ref(v___x_2374_);
v___x_2407_ = l_Lean_Syntax_node5(v_a_2366_, v___x_2388_, v___x_2390_, v___x_2391_, v___x_2374_, v___x_2404_, v___x_2406_);
v___x_2408_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2407_);
v___x_2409_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__11));
v___x_2410_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2409_);
v___x_2411_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2410_, v___x_2386_, v___x_2306_);
v___x_2412_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2411_);
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v_a_2366_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__13));
v___x_2416_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2415_);
v___x_2417_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__14));
v___x_2418_ = l_Lean_Name_mkStr4(v___x_2262_, v___x_2263_, v___x_2264_, v___x_2417_);
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_2420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_a_2366_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2266_);
v___x_2422_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2421_);
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_2424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2366_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node4(v_a_2366_, v___x_2418_, v___x_2420_, v___x_2422_, v___x_2424_, v_body_2267_);
v___x_2426_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2384_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2416_, v___x_2426_);
v___x_2428_ = l_Lean_Syntax_node6(v_a_2366_, v___x_2382_, v___x_2383_, v___x_2386_, v___x_2408_, v___x_2412_, v___x_2414_, v___x_2427_);
lean_inc_ref(v___x_2376_);
lean_inc_ref(v___x_2372_);
lean_inc_ref(v___x_2371_);
v___x_2429_ = l_Lean_Syntax_node5(v_a_2366_, v___x_2378_, v___x_2380_, v___x_2371_, v___x_2372_, v___x_2376_, v___x_2428_);
v___x_2430_ = l_Lean_Syntax_node7(v_a_2366_, v___x_2368_, v___x_2370_, v___x_2371_, v___x_2372_, v___x_2374_, v_rhs_2257_, v___x_2376_, v___x_2429_);
lean_inc(v_ref_2291_);
v_term_2277_ = v___x_2430_;
v___y_2278_ = v___y_2268_;
v___y_2279_ = v___y_2269_;
v___y_2280_ = v___y_2270_;
v___y_2281_ = v___y_2271_;
v___y_2282_ = v___y_2272_;
v___y_2283_ = v___y_2273_;
v_ref_2284_ = v_ref_2291_;
v___y_2285_ = v___y_2274_;
goto v___jp_2276_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2364_);
lean_dec(v___x_2306_);
lean_dec(v___x_2301_);
lean_dec(v_body_2267_);
lean_dec(v___x_2266_);
lean_dec_ref(v___x_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec_ref(v_a_2260_);
lean_dec(v_rhs_2257_);
v_a_2431_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2365_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2365_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v___x_2306_);
lean_dec(v___x_2301_);
lean_dec(v_body_2267_);
lean_dec(v___x_2266_);
lean_dec_ref(v___f_2265_);
lean_dec_ref(v___x_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec_ref(v_a_2260_);
lean_dec(v_rhs_2257_);
v_a_2439_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2363_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2363_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
v___jp_2276_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_a_2260_);
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_box(v___x_2261_);
lean_inc(v_term_2277_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 12, 4);
lean_closure_set(v___f_2289_, 0, v_term_2277_);
lean_closure_set(v___f_2289_, 1, v___x_2286_);
lean_closure_set(v___f_2289_, 2, v___x_2288_);
lean_closure_set(v___f_2289_, 3, v___x_2287_);
v___x_2290_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_ref_2284_, v_term_2277_, v___f_2289_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2285_);
return v___x_2290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed(lean_object** _args){
lean_object* v_rhs_2447_ = _args[0];
lean_object* v___x_2448_ = _args[1];
lean_object* v_config_2449_ = _args[2];
lean_object* v_a_2450_ = _args[3];
lean_object* v___x_2451_ = _args[4];
lean_object* v___x_2452_ = _args[5];
lean_object* v___x_2453_ = _args[6];
lean_object* v___x_2454_ = _args[7];
lean_object* v___f_2455_ = _args[8];
lean_object* v___x_2456_ = _args[9];
lean_object* v_body_2457_ = _args[10];
lean_object* v___y_2458_ = _args[11];
lean_object* v___y_2459_ = _args[12];
lean_object* v___y_2460_ = _args[13];
lean_object* v___y_2461_ = _args[14];
lean_object* v___y_2462_ = _args[15];
lean_object* v___y_2463_ = _args[16];
lean_object* v___y_2464_ = _args[17];
lean_object* v___y_2465_ = _args[18];
_start:
{
uint8_t v___x_100276__boxed_2466_; uint8_t v___x_100278__boxed_2467_; lean_object* v_res_2468_; 
v___x_100276__boxed_2466_ = lean_unbox(v___x_2448_);
v___x_100278__boxed_2467_ = lean_unbox(v___x_2451_);
v_res_2468_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__7(v_rhs_2447_, v___x_100276__boxed_2466_, v_config_2449_, v_a_2450_, v___x_100278__boxed_2467_, v___x_2452_, v___x_2453_, v___x_2454_, v___f_2455_, v___x_2456_, v_body_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(lean_object* v_x_2469_, lean_object* v___y_2470_){
_start:
{
if (lean_obj_tag(v_x_2469_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; 
v_a_2471_ = lean_ctor_get(v_x_2469_, 0);
lean_inc(v_a_2471_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2471_);
lean_ctor_set(v___x_2472_, 1, v___y_2470_);
return v___x_2472_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v_x_2469_, 0);
lean_inc(v_a_2473_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2473_);
lean_ctor_set(v___x_2474_, 1, v___y_2470_);
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg___boxed(lean_object* v_x_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_2475_, v___y_2476_);
lean_dec_ref(v_x_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(lean_object* v_env_2478_, lean_object* v_stx_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2478_, v_stx_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
if (lean_obj_tag(v_a_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2492_; 
v_a_2484_ = lean_ctor_get(v___x_2482_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2493_);
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2492_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2492_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_box(0);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2488_);
v___x_2490_ = v___x_2486_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_a_2484_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v_val_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2522_; 
v_val_2494_ = lean_ctor_get(v_a_2483_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_a_2483_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2496_ = v_a_2483_;
v_isShared_2497_ = v_isSharedCheck_2522_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_val_2494_);
lean_dec(v_a_2483_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2522_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_snd_2498_; 
v_snd_2498_ = lean_ctor_get(v_val_2494_, 1);
lean_inc(v_snd_2498_);
lean_dec(v_val_2494_);
if (lean_obj_tag(v_snd_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2508_; 
lean_del_object(v___x_2496_);
v_a_2499_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2482_, 2);
v_a_2500_ = lean_ctor_get(v_snd_2498_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_snd_2498_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2502_ = v_snd_2498_;
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v_snd_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2508_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2505_, v_a_2499_);
lean_dec_ref(v___x_2505_);
return v___x_2506_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2521_; 
v_a_2509_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2482_, 2);
v_a_2510_ = lean_ctor_get(v_snd_2498_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_snd_2498_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2512_ = v_snd_2498_;
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v_snd_2498_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v_a_2510_);
v___x_2515_ = v___x_2496_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2515_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v___x_2517_, v_a_2509_);
lean_dec_ref(v___x_2517_);
return v___x_2518_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2523_ = lean_ctor_get(v___x_2482_, 0);
v_a_2524_ = lean_ctor_get(v___x_2482_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2482_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_inc(v_a_2523_);
lean_dec(v___x_2482_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2523_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed(lean_object* v_env_2532_, lean_object* v_stx_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0(v_env_2532_, v_stx_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(lean_object* v_currNamespace_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_currNamespace_2537_);
lean_ctor_set(v___x_2540_, 1, v___y_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed(lean_object* v_currNamespace_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3(v_currNamespace_2541_, v___y_2542_, v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(lean_object* v_env_2545_, lean_object* v_currNamespace_2546_, lean_object* v_openDecls_2547_, lean_object* v_n_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = l_Lean_ResolveName_resolveNamespace(v_env_2545_, v_currNamespace_2546_, v_openDecls_2547_, v_n_2548_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
lean_ctor_set(v___x_2552_, 1, v___y_2550_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed(lean_object* v_env_2553_, lean_object* v_currNamespace_2554_, lean_object* v_openDecls_2555_, lean_object* v_n_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2(v_env_2553_, v_currNamespace_2554_, v_openDecls_2555_, v_n_2556_, v___y_2557_, v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(lean_object* v_env_2560_, lean_object* v_declName_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v___x_2564_; lean_object* v_env_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; uint8_t v___x_2568_; 
v___x_2564_ = 0;
v_env_2565_ = l_Lean_Environment_setExporting(v_env_2560_, v___x_2564_);
lean_inc(v_declName_2561_);
v___x_2566_ = l_Lean_mkPrivateName(v_env_2565_, v_declName_2561_);
v___x_2567_ = 1;
lean_inc_ref(v_env_2565_);
v___x_2568_ = l_Lean_Environment_contains(v_env_2565_, v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2569_ = l_Lean_privateToUserName(v_declName_2561_);
v___x_2570_ = l_Lean_Environment_contains(v_env_2565_, v___x_2569_, v___x_2567_);
v___x_2571_ = lean_box(v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___y_2563_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref(v_env_2565_);
lean_dec(v_declName_2561_);
v___x_2573_ = lean_box(v___x_2568_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v___y_2563_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed(lean_object* v_env_2575_, lean_object* v_declName_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1(v_env_2575_, v_declName_2576_, v___y_2577_, v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2579_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2580_; double v___x_2581_; 
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_float_of_nat(v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(lean_object* v_cls_2584_, lean_object* v_msg_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_ref_2591_; lean_object* v___x_2592_; lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2637_; 
v_ref_2591_ = lean_ctor_get(v___y_2588_, 5);
v___x_2592_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msg_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2637_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2637_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v_traceState_2598_; lean_object* v_env_2599_; lean_object* v_nextMacroScope_2600_; lean_object* v_ngen_2601_; lean_object* v_auxDeclNGen_2602_; lean_object* v_cache_2603_; lean_object* v_messages_2604_; lean_object* v_infoState_2605_; lean_object* v_snapshotTasks_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2636_; 
v___x_2597_ = lean_st_ref_take(v___y_2589_);
v_traceState_2598_ = lean_ctor_get(v___x_2597_, 4);
v_env_2599_ = lean_ctor_get(v___x_2597_, 0);
v_nextMacroScope_2600_ = lean_ctor_get(v___x_2597_, 1);
v_ngen_2601_ = lean_ctor_get(v___x_2597_, 2);
v_auxDeclNGen_2602_ = lean_ctor_get(v___x_2597_, 3);
v_cache_2603_ = lean_ctor_get(v___x_2597_, 5);
v_messages_2604_ = lean_ctor_get(v___x_2597_, 6);
v_infoState_2605_ = lean_ctor_get(v___x_2597_, 7);
v_snapshotTasks_2606_ = lean_ctor_get(v___x_2597_, 8);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2608_ = v___x_2597_;
v_isShared_2609_ = v_isSharedCheck_2636_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_snapshotTasks_2606_);
lean_inc(v_infoState_2605_);
lean_inc(v_messages_2604_);
lean_inc(v_cache_2603_);
lean_inc(v_traceState_2598_);
lean_inc(v_auxDeclNGen_2602_);
lean_inc(v_ngen_2601_);
lean_inc(v_nextMacroScope_2600_);
lean_inc(v_env_2599_);
lean_dec(v___x_2597_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2636_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
uint64_t v_tid_2610_; lean_object* v_traces_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2635_; 
v_tid_2610_ = lean_ctor_get_uint64(v_traceState_2598_, sizeof(void*)*1);
v_traces_2611_ = lean_ctor_get(v_traceState_2598_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_traceState_2598_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2613_ = v_traceState_2598_;
v_isShared_2614_ = v_isSharedCheck_2635_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_traces_2611_);
lean_dec(v_traceState_2598_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2635_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; double v___x_2616_; uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__0);
v___x_2617_ = 0;
v___x_2618_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2619_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2619_, 0, v_cls_2584_);
lean_ctor_set(v___x_2619_, 1, v___x_2615_);
lean_ctor_set(v___x_2619_, 2, v___x_2618_);
lean_ctor_set_float(v___x_2619_, sizeof(void*)*3, v___x_2616_);
lean_ctor_set_float(v___x_2619_, sizeof(void*)*3 + 8, v___x_2616_);
lean_ctor_set_uint8(v___x_2619_, sizeof(void*)*3 + 16, v___x_2617_);
v___x_2620_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___closed__1));
v___x_2621_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v_a_2593_);
lean_ctor_set(v___x_2621_, 2, v___x_2620_);
lean_inc(v_ref_2591_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v_ref_2591_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = l_Lean_PersistentArray_push___redArg(v_traces_2611_, v___x_2622_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2623_);
v___x_2625_ = v___x_2613_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2623_);
lean_ctor_set_uint64(v_reuseFailAlloc_2634_, sizeof(void*)*1, v_tid_2610_);
v___x_2625_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 4, v___x_2625_);
v___x_2627_ = v___x_2608_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_env_2599_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_nextMacroScope_2600_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_ngen_2601_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v_auxDeclNGen_2602_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2633_, 5, v_cache_2603_);
lean_ctor_set(v_reuseFailAlloc_2633_, 6, v_messages_2604_);
lean_ctor_set(v_reuseFailAlloc_2633_, 7, v_infoState_2605_);
lean_ctor_set(v_reuseFailAlloc_2633_, 8, v_snapshotTasks_2606_);
v___x_2627_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2628_ = lean_st_ref_set(v___y_2589_, v___x_2627_);
v___x_2629_ = lean_box(0);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2629_);
v___x_2631_ = v___x_2595_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg___boxed(lean_object* v_cls_2638_, lean_object* v_msg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2638_, v_msg_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(lean_object* v_as_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
if (lean_obj_tag(v_as_2649_) == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
else
{
lean_object* v_options_2660_; uint8_t v_hasTrace_2661_; 
v_options_2660_ = lean_ctor_get(v___y_2655_, 2);
v_hasTrace_2661_ = lean_ctor_get_uint8(v_options_2660_, sizeof(void*)*1);
if (v_hasTrace_2661_ == 0)
{
lean_object* v_tail_2662_; 
v_tail_2662_ = lean_ctor_get(v_as_2649_, 1);
lean_inc(v_tail_2662_);
lean_dec_ref_known(v_as_2649_, 2);
v_as_2649_ = v_tail_2662_;
goto _start;
}
else
{
lean_object* v_head_2664_; lean_object* v_tail_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v_inheritedTraceOptions_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_head_2664_ = lean_ctor_get(v_as_2649_, 0);
lean_inc(v_head_2664_);
v_tail_2665_ = lean_ctor_get(v_as_2649_, 1);
lean_inc(v_tail_2665_);
lean_dec_ref_known(v_as_2649_, 2);
v_fst_2666_ = lean_ctor_get(v_head_2664_, 0);
lean_inc_n(v_fst_2666_, 2);
v_snd_2667_ = lean_ctor_get(v_head_2664_, 1);
lean_inc(v_snd_2667_);
lean_dec(v_head_2664_);
v_inheritedTraceOptions_2668_ = lean_ctor_get(v___y_2655_, 13);
v___x_2669_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2670_ = l_Lean_Name_append(v___x_2669_, v_fst_2666_);
v___x_2671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2668_, v_options_2660_, v___x_2670_);
lean_dec(v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec(v_snd_2667_);
lean_dec(v_fst_2666_);
v_as_2649_ = v_tail_2665_;
goto _start;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_snd_2667_);
v___x_2674_ = l_Lean_MessageData_ofFormat(v___x_2673_);
v___x_2675_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_fst_2666_, v___x_2674_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_dec_ref_known(v___x_2675_, 1);
v_as_2649_ = v_tail_2665_;
goto _start;
}
else
{
lean_dec(v_tail_2665_);
return v___x_2675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___boxed(lean_object* v_as_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v_as_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(lean_object* v_keys_2687_, lean_object* v_i_2688_, lean_object* v_k_2689_){
_start:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = lean_array_get_size(v_keys_2687_);
v___x_2691_ = lean_nat_dec_lt(v_i_2688_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec(v_i_2688_);
return v___x_2691_;
}
else
{
lean_object* v_k_x27_2692_; uint8_t v___x_2693_; 
v_k_x27_2692_ = lean_array_fget_borrowed(v_keys_2687_, v_i_2688_);
v___x_2693_ = l_Lean_instBEqExtraModUse_beq(v_k_2689_, v_k_x27_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_nat_add(v_i_2688_, v___x_2694_);
lean_dec(v_i_2688_);
v_i_2688_ = v___x_2695_;
goto _start;
}
else
{
lean_dec(v_i_2688_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg___boxed(lean_object* v_keys_2697_, lean_object* v_i_2698_, lean_object* v_k_2699_){
_start:
{
uint8_t v_res_2700_; lean_object* v_r_2701_; 
v_res_2700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_2697_, v_i_2698_, v_k_2699_);
lean_dec_ref(v_k_2699_);
lean_dec_ref(v_keys_2697_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(lean_object* v_x_2702_, size_t v_x_2703_, lean_object* v_x_2704_){
_start:
{
if (lean_obj_tag(v_x_2702_) == 0)
{
lean_object* v_es_2705_; lean_object* v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v_j_2710_; lean_object* v___x_2711_; 
v_es_2705_ = lean_ctor_get(v_x_2702_, 0);
v___x_2706_ = lean_box(2);
v___x_2707_ = ((size_t)5ULL);
v___x_2708_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__1);
v___x_2709_ = lean_usize_land(v_x_2703_, v___x_2708_);
v_j_2710_ = lean_usize_to_nat(v___x_2709_);
v___x_2711_ = lean_array_get_borrowed(v___x_2706_, v_es_2705_, v_j_2710_);
lean_dec(v_j_2710_);
switch(lean_obj_tag(v___x_2711_))
{
case 0:
{
lean_object* v_key_2712_; uint8_t v___x_2713_; 
v_key_2712_ = lean_ctor_get(v___x_2711_, 0);
v___x_2713_ = l_Lean_instBEqExtraModUse_beq(v_x_2704_, v_key_2712_);
return v___x_2713_;
}
case 1:
{
lean_object* v_node_2714_; size_t v___x_2715_; 
v_node_2714_ = lean_ctor_get(v___x_2711_, 0);
v___x_2715_ = lean_usize_shift_right(v_x_2703_, v___x_2707_);
v_x_2702_ = v_node_2714_;
v_x_2703_ = v___x_2715_;
goto _start;
}
default: 
{
uint8_t v___x_2717_; 
v___x_2717_ = 0;
return v___x_2717_;
}
}
}
else
{
lean_object* v_ks_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_ks_2718_ = lean_ctor_get(v_x_2702_, 0);
v___x_2719_ = lean_unsigned_to_nat(0u);
v___x_2720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_ks_2718_, v___x_2719_, v_x_2704_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg___boxed(lean_object* v_x_2721_, lean_object* v_x_2722_, lean_object* v_x_2723_){
_start:
{
size_t v_x_101026__boxed_2724_; uint8_t v_res_2725_; lean_object* v_r_2726_; 
v_x_101026__boxed_2724_ = lean_unbox_usize(v_x_2722_);
lean_dec(v_x_2722_);
v_res_2725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2721_, v_x_101026__boxed_2724_, v_x_2723_);
lean_dec_ref(v_x_2723_);
lean_dec_ref(v_x_2721_);
v_r_2726_ = lean_box(v_res_2725_);
return v_r_2726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(lean_object* v_x_2727_, lean_object* v_x_2728_){
_start:
{
uint64_t v___x_2729_; size_t v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = l_Lean_instHashableExtraModUse_hash(v_x_2728_);
v___x_2730_ = lean_uint64_to_usize(v___x_2729_);
v___x_2731_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_2727_, v___x_2730_, v_x_2728_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg___boxed(lean_object* v_x_2732_, lean_object* v_x_2733_){
_start:
{
uint8_t v_res_2734_; lean_object* v_r_2735_; 
v_res_2734_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_2732_, v_x_2733_);
lean_dec_ref(v_x_2733_);
lean_dec_ref(v_x_2732_);
v_r_2735_ = lean_box(v_res_2734_);
return v_r_2735_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__1));
v___x_2739_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__0));
v___x_2740_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2739_, v___x_2738_);
return v___x_2740_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2741_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__3);
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
return v___x_2743_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__4);
v___x_2747_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
lean_ctor_set(v___x_2747_, 3, v___x_2746_);
lean_ctor_set(v___x_2747_, 4, v___x_2746_);
lean_ctor_set(v___x_2747_, 5, v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__9));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__11));
v___x_2756_ = l_Lean_stringToMessageData(v___x_2755_);
return v___x_2756_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14(void){
_start:
{
lean_object* v_cls_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v_cls_2759_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2760_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_2761_ = l_Lean_Name_append(v___x_2760_, v_cls_2759_);
return v___x_2761_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__15));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__17));
v___x_2767_ = l_Lean_stringToMessageData(v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(lean_object* v_mod_2772_, uint8_t v_isMeta_2773_, lean_object* v_hint_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; lean_object* v_env_2784_; uint8_t v_isExporting_2785_; lean_object* v___x_2786_; lean_object* v_env_2787_; lean_object* v___x_2788_; lean_object* v_entry_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2783_ = lean_st_ref_get(v___y_2781_);
v_env_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc_ref(v_env_2784_);
lean_dec(v___x_2783_);
v_isExporting_2785_ = lean_ctor_get_uint8(v_env_2784_, sizeof(void*)*8);
lean_dec_ref(v_env_2784_);
v___x_2786_ = lean_st_ref_get(v___y_2781_);
v_env_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc_ref(v_env_2787_);
lean_dec(v___x_2786_);
v___x_2788_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__2);
lean_inc(v_mod_2772_);
v_entry_2789_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2789_, 0, v_mod_2772_);
lean_ctor_set_uint8(v_entry_2789_, sizeof(void*)*1, v_isExporting_2785_);
lean_ctor_set_uint8(v_entry_2789_, sizeof(void*)*1 + 1, v_isMeta_2773_);
v___x_2790_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2791_ = lean_box(1);
v___x_2792_ = lean_box(0);
v___x_2835_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2788_, v___x_2790_, v_env_2787_, v___x_2791_, v___x_2792_);
v___x_2836_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v___x_2835_, v_entry_2789_);
lean_dec(v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v_options_2837_; uint8_t v_hasTrace_2838_; 
v_options_2837_ = lean_ctor_get(v___y_2780_, 2);
v_hasTrace_2838_ = lean_ctor_get_uint8(v_options_2837_, sizeof(void*)*1);
if (v_hasTrace_2838_ == 0)
{
lean_dec(v_hint_2774_);
lean_dec(v_mod_2772_);
v___y_2794_ = v___y_2779_;
v___y_2795_ = v___y_2781_;
goto v___jp_2793_;
}
else
{
lean_object* v_inheritedTraceOptions_2839_; lean_object* v_cls_2840_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_inheritedTraceOptions_2839_ = lean_ctor_get(v___y_2780_, 13);
v_cls_2840_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__8));
v___x_2860_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__14);
v___x_2861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2839_, v_options_2837_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_dec(v_hint_2774_);
lean_dec(v_mod_2772_);
v___y_2794_ = v___y_2779_;
v___y_2795_ = v___y_2781_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2862_; lean_object* v___y_2864_; 
v___x_2862_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__16);
if (v_isExporting_2785_ == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__21));
v___y_2864_ = v___x_2871_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2872_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__22));
v___y_2864_ = v___x_2872_;
goto v___jp_2863_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_inc_ref(v___y_2864_);
v___x_2865_ = l_Lean_stringToMessageData(v___y_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2862_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__18);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
if (v_isMeta_2773_ == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__19));
v___y_2847_ = v___x_2868_;
v___y_2848_ = v___x_2869_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2870_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__20));
v___y_2847_ = v___x_2868_;
v___y_2848_ = v___x_2870_;
goto v___jp_2846_;
}
}
}
v___jp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___y_2842_);
lean_ctor_set(v___x_2844_, 1, v___y_2843_);
v___x_2845_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_2840_, v___x_2844_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref_known(v___x_2845_, 1);
v___y_2794_ = v___y_2779_;
v___y_2795_ = v___y_2781_;
goto v___jp_2793_;
}
else
{
lean_dec_ref_known(v_entry_2789_, 1);
return v___x_2845_;
}
}
v___jp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
lean_inc_ref(v___y_2848_);
v___x_2849_ = l_Lean_stringToMessageData(v___y_2848_);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___y_2847_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__10);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = l_Lean_MessageData_ofName(v_mod_2772_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_Name_isAnonymous(v_hint_2774_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__12);
v___x_2857_ = l_Lean_MessageData_ofName(v_hint_2774_);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___y_2842_ = v___x_2854_;
v___y_2843_ = v___x_2858_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v_hint_2774_);
v___x_2859_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__13);
v___y_2842_ = v___x_2854_;
v___y_2843_ = v___x_2859_;
goto v___jp_2841_;
}
}
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref_known(v_entry_2789_, 1);
lean_dec(v_hint_2774_);
lean_dec(v_mod_2772_);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
v___jp_2793_:
{
lean_object* v___x_2796_; lean_object* v_toEnvExtension_2797_; lean_object* v_env_2798_; lean_object* v_nextMacroScope_2799_; lean_object* v_ngen_2800_; lean_object* v_auxDeclNGen_2801_; lean_object* v_traceState_2802_; lean_object* v_messages_2803_; lean_object* v_infoState_2804_; lean_object* v_snapshotTasks_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2833_; 
v___x_2796_ = lean_st_ref_take(v___y_2795_);
v_toEnvExtension_2797_ = lean_ctor_get(v___x_2790_, 0);
v_env_2798_ = lean_ctor_get(v___x_2796_, 0);
v_nextMacroScope_2799_ = lean_ctor_get(v___x_2796_, 1);
v_ngen_2800_ = lean_ctor_get(v___x_2796_, 2);
v_auxDeclNGen_2801_ = lean_ctor_get(v___x_2796_, 3);
v_traceState_2802_ = lean_ctor_get(v___x_2796_, 4);
v_messages_2803_ = lean_ctor_get(v___x_2796_, 6);
v_infoState_2804_ = lean_ctor_get(v___x_2796_, 7);
v_snapshotTasks_2805_ = lean_ctor_get(v___x_2796_, 8);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v___x_2796_, 5);
lean_dec(v_unused_2834_);
v___x_2807_ = v___x_2796_;
v_isShared_2808_ = v_isSharedCheck_2833_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_snapshotTasks_2805_);
lean_inc(v_infoState_2804_);
lean_inc(v_messages_2803_);
lean_inc(v_traceState_2802_);
lean_inc(v_auxDeclNGen_2801_);
lean_inc(v_ngen_2800_);
lean_inc(v_nextMacroScope_2799_);
lean_inc(v_env_2798_);
lean_dec(v___x_2796_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2833_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_asyncMode_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v_asyncMode_2809_ = lean_ctor_get(v_toEnvExtension_2797_, 2);
v___x_2810_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2790_, v_env_2798_, v_entry_2789_, v_asyncMode_2809_, v___x_2792_);
v___x_2811_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__5);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 5, v___x_2811_);
lean_ctor_set(v___x_2807_, 0, v___x_2810_);
v___x_2813_ = v___x_2807_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_nextMacroScope_2799_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_ngen_2800_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_auxDeclNGen_2801_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_traceState_2802_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2832_, 6, v_messages_2803_);
lean_ctor_set(v_reuseFailAlloc_2832_, 7, v_infoState_2804_);
lean_ctor_set(v_reuseFailAlloc_2832_, 8, v_snapshotTasks_2805_);
v___x_2813_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_mctx_2816_; lean_object* v_zetaDeltaFVarIds_2817_; lean_object* v_postponed_2818_; lean_object* v_diag_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2830_; 
v___x_2814_ = lean_st_ref_set(v___y_2795_, v___x_2813_);
v___x_2815_ = lean_st_ref_take(v___y_2794_);
v_mctx_2816_ = lean_ctor_get(v___x_2815_, 0);
v_zetaDeltaFVarIds_2817_ = lean_ctor_get(v___x_2815_, 2);
v_postponed_2818_ = lean_ctor_get(v___x_2815_, 3);
v_diag_2819_ = lean_ctor_get(v___x_2815_, 4);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2815_, 1);
lean_dec(v_unused_2831_);
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2830_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_diag_2819_);
lean_inc(v_postponed_2818_);
lean_inc(v_zetaDeltaFVarIds_2817_);
lean_inc(v_mctx_2816_);
lean_dec(v___x_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2830_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___closed__6);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_mctx_2816_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_zetaDeltaFVarIds_2817_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_postponed_2818_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_diag_2819_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_st_ref_set(v___y_2794_, v___x_2825_);
v___x_2827_ = lean_box(0);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17___boxed(lean_object* v_mod_2875_, lean_object* v_isMeta_2876_, lean_object* v_hint_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_isMeta_boxed_2886_; lean_object* v_res_2887_; 
v_isMeta_boxed_2886_ = lean_unbox(v_isMeta_2876_);
v_res_2887_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_mod_2875_, v_isMeta_boxed_2886_, v_hint_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v___y_2878_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(lean_object* v___x_2888_, lean_object* v_declName_2889_, lean_object* v_as_2890_, size_t v_sz_2891_, size_t v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v_declName_2889_);
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_b_2893_);
return v___x_2903_;
}
else
{
lean_object* v___x_2904_; lean_object* v_modules_2905_; lean_object* v___x_2906_; lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v_toImport_2909_; lean_object* v_module_2910_; uint8_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2904_ = l_Lean_Environment_header(v___x_2888_);
v_modules_2905_ = lean_ctor_get(v___x_2904_, 3);
lean_inc_ref(v_modules_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2907_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
v___x_2908_ = lean_array_get(v___x_2906_, v_modules_2905_, v_a_2907_);
lean_dec_ref(v_modules_2905_);
v_toImport_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_toImport_2909_);
lean_dec(v___x_2908_);
v_module_2910_ = lean_ctor_get(v_toImport_2909_, 0);
lean_inc(v_module_2910_);
lean_dec_ref(v_toImport_2909_);
v___x_2911_ = 0;
lean_inc(v_declName_2889_);
v___x_2912_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_2910_, v___x_2911_, v_declName_2889_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; size_t v___x_2914_; size_t v___x_2915_; 
lean_dec_ref_known(v___x_2912_, 1);
v___x_2913_ = lean_box(0);
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_add(v_i_2892_, v___x_2914_);
v_i_2892_ = v___x_2915_;
v_b_2893_ = v___x_2913_;
goto _start;
}
else
{
lean_dec(v_declName_2889_);
return v___x_2912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18___boxed(lean_object* v___x_2917_, lean_object* v_declName_2918_, lean_object* v_as_2919_, lean_object* v_sz_2920_, lean_object* v_i_2921_, lean_object* v_b_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
size_t v_sz_boxed_2931_; size_t v_i_boxed_2932_; lean_object* v_res_2933_; 
v_sz_boxed_2931_ = lean_unbox_usize(v_sz_2920_);
lean_dec(v_sz_2920_);
v_i_boxed_2932_ = lean_unbox_usize(v_i_2921_);
lean_dec(v_i_2921_);
v_res_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v___x_2917_, v_declName_2918_, v_as_2919_, v_sz_boxed_2931_, v_i_boxed_2932_, v_b_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v_as_2919_);
lean_dec_ref(v___x_2917_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(lean_object* v_a_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v_key_2937_; lean_object* v_value_2938_; lean_object* v_tail_2939_; uint8_t v___x_2940_; 
v_key_2937_ = lean_ctor_get(v_x_2935_, 0);
v_value_2938_ = lean_ctor_get(v_x_2935_, 1);
v_tail_2939_ = lean_ctor_get(v_x_2935_, 2);
v___x_2940_ = lean_name_eq(v_key_2937_, v_a_2934_);
if (v___x_2940_ == 0)
{
v_x_2935_ = v_tail_2939_;
goto _start;
}
else
{
lean_object* v___x_2942_; 
lean_inc(v_value_2938_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_value_2938_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg___boxed(lean_object* v_a_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2943_, v_x_2944_);
lean_dec(v_x_2944_);
lean_dec(v_a_2943_);
return v_res_2945_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2946_; uint64_t v___x_2947_; 
v___x_2946_ = lean_unsigned_to_nat(1723u);
v___x_2947_ = lean_uint64_of_nat(v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(lean_object* v_m_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_buckets_2950_; lean_object* v___x_2951_; uint64_t v___y_2953_; 
v_buckets_2950_ = lean_ctor_get(v_m_2948_, 1);
v___x_2951_ = lean_array_get_size(v_buckets_2950_);
if (lean_obj_tag(v_a_2949_) == 0)
{
uint64_t v___x_2967_; 
v___x_2967_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___closed__0);
v___y_2953_ = v___x_2967_;
goto v___jp_2952_;
}
else
{
uint64_t v_hash_2968_; 
v_hash_2968_ = lean_ctor_get_uint64(v_a_2949_, sizeof(void*)*2);
v___y_2953_ = v_hash_2968_;
goto v___jp_2952_;
}
v___jp_2952_:
{
uint64_t v___x_2954_; uint64_t v___x_2955_; uint64_t v_fold_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2954_ = 32ULL;
v___x_2955_ = lean_uint64_shift_right(v___y_2953_, v___x_2954_);
v_fold_2956_ = lean_uint64_xor(v___y_2953_, v___x_2955_);
v___x_2957_ = 16ULL;
v___x_2958_ = lean_uint64_shift_right(v_fold_2956_, v___x_2957_);
v___x_2959_ = lean_uint64_xor(v_fold_2956_, v___x_2958_);
v___x_2960_ = lean_uint64_to_usize(v___x_2959_);
v___x_2961_ = lean_usize_of_nat(v___x_2951_);
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_sub(v___x_2961_, v___x_2962_);
v___x_2964_ = lean_usize_land(v___x_2960_, v___x_2963_);
v___x_2965_ = lean_array_uget_borrowed(v_buckets_2950_, v___x_2964_);
v___x_2966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_2949_, v___x_2965_);
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg___boxed(lean_object* v_m_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_2969_, v_a_2970_);
lean_dec(v_a_2970_);
lean_dec_ref(v_m_2969_);
return v_res_2971_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2(void){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__1));
v___x_2975_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__0));
v___x_2976_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2975_, v___x_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(lean_object* v_declName_2979_, uint8_t v_isMeta_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; lean_object* v_env_2993_; lean_object* v___y_2995_; lean_object* v___x_3008_; 
v___x_2989_ = lean_st_ref_get(v___y_2987_);
v_env_2993_ = lean_ctor_get(v___x_2989_, 0);
lean_inc_ref(v_env_2993_);
lean_dec(v___x_2989_);
v___x_3008_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2993_, v_declName_2979_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_dec_ref(v_env_2993_);
lean_dec(v_declName_2979_);
goto v___jp_2990_;
}
else
{
lean_object* v_val_3009_; lean_object* v___x_3010_; lean_object* v_modules_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_val_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_val_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Environment_header(v_env_2993_);
v_modules_3011_ = lean_ctor_get(v___x_3010_, 3);
lean_inc_ref(v_modules_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = lean_array_get_size(v_modules_3011_);
v___x_3013_ = lean_nat_dec_lt(v_val_3009_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec_ref(v_modules_3011_);
lean_dec(v_val_3009_);
lean_dec_ref(v_env_2993_);
lean_dec(v_declName_2979_);
goto v___jp_2990_;
}
else
{
lean_object* v___x_3014_; lean_object* v_env_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___y_3019_; 
v___x_3014_ = lean_st_ref_get(v___y_2987_);
v_env_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_ref(v_env_3015_);
lean_dec(v___x_3014_);
v___x_3016_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__2);
v___x_3017_ = lean_array_fget(v_modules_3011_, v_val_3009_);
lean_dec(v_val_3009_);
lean_dec_ref(v_modules_3011_);
if (v_isMeta_2980_ == 0)
{
lean_dec_ref(v_env_3015_);
v___y_3019_ = v_isMeta_2980_;
goto v___jp_3018_;
}
else
{
uint8_t v___x_3030_; 
lean_inc(v_declName_2979_);
v___x_3030_ = l_Lean_isMarkedMeta(v_env_3015_, v_declName_2979_);
if (v___x_3030_ == 0)
{
v___y_3019_ = v_isMeta_2980_;
goto v___jp_3018_;
}
else
{
uint8_t v___x_3031_; 
v___x_3031_ = 0;
v___y_3019_ = v___x_3031_;
goto v___jp_3018_;
}
}
v___jp_3018_:
{
lean_object* v_toImport_3020_; lean_object* v_module_3021_; lean_object* v___x_3022_; 
v_toImport_3020_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_toImport_3020_);
lean_dec(v___x_3017_);
v_module_3021_ = lean_ctor_get(v_toImport_3020_, 0);
lean_inc(v_module_3021_);
lean_dec_ref(v_toImport_3020_);
lean_inc(v_declName_2979_);
v___x_3022_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17(v_module_3021_, v___y_3019_, v_declName_2979_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_dec_ref_known(v___x_3022_, 1);
v___x_3023_ = l_Lean_indirectModUseExt;
v___x_3024_ = lean_box(1);
v___x_3025_ = lean_box(0);
lean_inc_ref(v_env_2993_);
v___x_3026_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3016_, v___x_3023_, v_env_2993_, v___x_3024_, v___x_3025_);
v___x_3027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v___x_3026_, v_declName_2979_);
lean_dec(v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___closed__3));
v___y_2995_ = v___x_3028_;
goto v___jp_2994_;
}
else
{
lean_object* v_val_3029_; 
v_val_3029_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_val_3029_);
lean_dec_ref_known(v___x_3027_, 1);
v___y_2995_ = v_val_3029_;
goto v___jp_2994_;
}
}
else
{
lean_dec_ref(v_env_2993_);
lean_dec(v_declName_2979_);
return v___x_3022_;
}
}
}
}
v___jp_2990_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
v___jp_2994_:
{
lean_object* v___x_2996_; size_t v_sz_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = lean_box(0);
v_sz_2997_ = lean_array_size(v___y_2995_);
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__18(v_env_2993_, v_declName_2979_, v___y_2995_, v_sz_2997_, v___x_2998_, v___x_2996_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v_env_2993_);
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
lean_ctor_set(v___x_3001_, 0, v___x_2996_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2996_);
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
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13___boxed(lean_object* v_declName_3032_, lean_object* v_isMeta_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
uint8_t v_isMeta_boxed_3042_; lean_object* v_res_3043_; 
v_isMeta_boxed_3042_ = lean_unbox(v_isMeta_3033_);
v_res_3043_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_declName_3032_, v_isMeta_boxed_3042_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(lean_object* v_as_x27_3044_, lean_object* v_b_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
if (lean_obj_tag(v_as_x27_3044_) == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_b_3045_);
return v___x_3054_;
}
else
{
lean_object* v_head_3055_; lean_object* v_tail_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v_head_3055_ = lean_ctor_get(v_as_x27_3044_, 0);
v_tail_3056_ = lean_ctor_get(v_as_x27_3044_, 1);
v___x_3057_ = 1;
lean_inc(v_head_3055_);
v___x_3058_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13(v_head_3055_, v___x_3057_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
lean_dec_ref_known(v___x_3058_, 1);
v___x_3059_ = lean_box(0);
v_as_x27_3044_ = v_tail_3056_;
v_b_3045_ = v___x_3059_;
goto _start;
}
else
{
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg___boxed(lean_object* v_as_x27_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3061_, v_b_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v_as_x27_3061_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(lean_object* v_env_3072_, lean_object* v_options_3073_, lean_object* v_currNamespace_3074_, lean_object* v_openDecls_3075_, lean_object* v_n_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = l_Lean_ResolveName_resolveGlobalName(v_env_3072_, v_options_3073_, v_currNamespace_3074_, v_openDecls_3075_, v_n_3076_);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
lean_ctor_set(v___x_3080_, 1, v___y_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed(lean_object* v_env_3081_, lean_object* v_options_3082_, lean_object* v_currNamespace_3083_, lean_object* v_openDecls_3084_, lean_object* v_n_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4(v_env_3081_, v_options_3082_, v_currNamespace_3083_, v_openDecls_3084_, v_n_3085_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v_options_3082_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(lean_object* v_ref_3089_, lean_object* v_msg_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_fileName_3096_; lean_object* v_fileMap_3097_; lean_object* v_options_3098_; lean_object* v_currRecDepth_3099_; lean_object* v_maxRecDepth_3100_; lean_object* v_ref_3101_; lean_object* v_currNamespace_3102_; lean_object* v_openDecls_3103_; lean_object* v_initHeartbeats_3104_; lean_object* v_maxHeartbeats_3105_; lean_object* v_quotContext_3106_; lean_object* v_currMacroScope_3107_; uint8_t v_diag_3108_; lean_object* v_cancelTk_x3f_3109_; uint8_t v_suppressElabErrors_3110_; lean_object* v_inheritedTraceOptions_3111_; lean_object* v_ref_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_fileName_3096_ = lean_ctor_get(v___y_3093_, 0);
v_fileMap_3097_ = lean_ctor_get(v___y_3093_, 1);
v_options_3098_ = lean_ctor_get(v___y_3093_, 2);
v_currRecDepth_3099_ = lean_ctor_get(v___y_3093_, 3);
v_maxRecDepth_3100_ = lean_ctor_get(v___y_3093_, 4);
v_ref_3101_ = lean_ctor_get(v___y_3093_, 5);
v_currNamespace_3102_ = lean_ctor_get(v___y_3093_, 6);
v_openDecls_3103_ = lean_ctor_get(v___y_3093_, 7);
v_initHeartbeats_3104_ = lean_ctor_get(v___y_3093_, 8);
v_maxHeartbeats_3105_ = lean_ctor_get(v___y_3093_, 9);
v_quotContext_3106_ = lean_ctor_get(v___y_3093_, 10);
v_currMacroScope_3107_ = lean_ctor_get(v___y_3093_, 11);
v_diag_3108_ = lean_ctor_get_uint8(v___y_3093_, sizeof(void*)*14);
v_cancelTk_x3f_3109_ = lean_ctor_get(v___y_3093_, 12);
v_suppressElabErrors_3110_ = lean_ctor_get_uint8(v___y_3093_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3111_ = lean_ctor_get(v___y_3093_, 13);
v_ref_3112_ = l_Lean_replaceRef(v_ref_3089_, v_ref_3101_);
lean_inc_ref(v_inheritedTraceOptions_3111_);
lean_inc(v_cancelTk_x3f_3109_);
lean_inc(v_currMacroScope_3107_);
lean_inc(v_quotContext_3106_);
lean_inc(v_maxHeartbeats_3105_);
lean_inc(v_initHeartbeats_3104_);
lean_inc(v_openDecls_3103_);
lean_inc(v_currNamespace_3102_);
lean_inc(v_maxRecDepth_3100_);
lean_inc(v_currRecDepth_3099_);
lean_inc_ref(v_options_3098_);
lean_inc_ref(v_fileMap_3097_);
lean_inc_ref(v_fileName_3096_);
v___x_3113_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3113_, 0, v_fileName_3096_);
lean_ctor_set(v___x_3113_, 1, v_fileMap_3097_);
lean_ctor_set(v___x_3113_, 2, v_options_3098_);
lean_ctor_set(v___x_3113_, 3, v_currRecDepth_3099_);
lean_ctor_set(v___x_3113_, 4, v_maxRecDepth_3100_);
lean_ctor_set(v___x_3113_, 5, v_ref_3112_);
lean_ctor_set(v___x_3113_, 6, v_currNamespace_3102_);
lean_ctor_set(v___x_3113_, 7, v_openDecls_3103_);
lean_ctor_set(v___x_3113_, 8, v_initHeartbeats_3104_);
lean_ctor_set(v___x_3113_, 9, v_maxHeartbeats_3105_);
lean_ctor_set(v___x_3113_, 10, v_quotContext_3106_);
lean_ctor_set(v___x_3113_, 11, v_currMacroScope_3107_);
lean_ctor_set(v___x_3113_, 12, v_cancelTk_x3f_3109_);
lean_ctor_set(v___x_3113_, 13, v_inheritedTraceOptions_3111_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*14, v_diag_3108_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*14 + 1, v_suppressElabErrors_3110_);
v___x_3114_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v_msg_3090_, v___y_3091_, v___y_3092_, v___x_3113_, v___y_3094_);
lean_dec_ref_known(v___x_3113_, 14);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg___boxed(lean_object* v_ref_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3115_, v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v_ref_3115_);
return v_res_3122_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = l_Lean_maxRecDepthErrorMessage;
v___x_3129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__3);
v___x_3131_ = l_Lean_MessageData_ofFormat(v___x_3130_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__4);
v___x_3133_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__2));
v___x_3134_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(lean_object* v_ref_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___closed__5);
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v_ref_3135_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg___boxed(lean_object* v_ref_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_env_3154_; lean_object* v_options_3155_; lean_object* v_currRecDepth_3156_; lean_object* v_maxRecDepth_3157_; lean_object* v_ref_3158_; lean_object* v_currNamespace_3159_; lean_object* v_openDecls_3160_; lean_object* v_quotContext_3161_; lean_object* v_currMacroScope_3162_; lean_object* v___x_3163_; lean_object* v_nextMacroScope_3164_; lean_object* v___f_3165_; lean_object* v___f_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___f_3169_; lean_object* v_methods_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3153_ = lean_st_ref_get(v___y_3151_);
v_env_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref_n(v_env_3154_, 4);
lean_dec(v___x_3153_);
v_options_3155_ = lean_ctor_get(v___y_3150_, 2);
v_currRecDepth_3156_ = lean_ctor_get(v___y_3150_, 3);
v_maxRecDepth_3157_ = lean_ctor_get(v___y_3150_, 4);
v_ref_3158_ = lean_ctor_get(v___y_3150_, 5);
v_currNamespace_3159_ = lean_ctor_get(v___y_3150_, 6);
v_openDecls_3160_ = lean_ctor_get(v___y_3150_, 7);
v_quotContext_3161_ = lean_ctor_get(v___y_3150_, 10);
v_currMacroScope_3162_ = lean_ctor_get(v___y_3150_, 11);
v___x_3163_ = lean_st_ref_get(v___y_3151_);
v_nextMacroScope_3164_ = lean_ctor_get(v___x_3163_, 1);
lean_inc(v_nextMacroScope_3164_);
lean_dec(v___x_3163_);
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3165_, 0, v_env_3154_);
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3166_, 0, v_env_3154_);
lean_inc_n(v_openDecls_3160_, 2);
lean_inc_n(v_currNamespace_3159_, 3);
v___f_3167_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3167_, 0, v_env_3154_);
lean_closure_set(v___f_3167_, 1, v_currNamespace_3159_);
lean_closure_set(v___f_3167_, 2, v_openDecls_3160_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3168_, 0, v_currNamespace_3159_);
lean_inc_ref(v_options_3155_);
v___f_3169_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3169_, 0, v_env_3154_);
lean_closure_set(v___f_3169_, 1, v_options_3155_);
lean_closure_set(v___f_3169_, 2, v_currNamespace_3159_);
lean_closure_set(v___f_3169_, 3, v_openDecls_3160_);
v_methods_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3170_, 0, v___f_3165_);
lean_ctor_set(v_methods_3170_, 1, v___f_3168_);
lean_ctor_set(v_methods_3170_, 2, v___f_3166_);
lean_ctor_set(v_methods_3170_, 3, v___f_3167_);
lean_ctor_set(v_methods_3170_, 4, v___f_3169_);
lean_inc(v_ref_3158_);
lean_inc(v_maxRecDepth_3157_);
lean_inc(v_currRecDepth_3156_);
lean_inc(v_currMacroScope_3162_);
lean_inc(v_quotContext_3161_);
v___x_3171_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3171_, 0, v_methods_3170_);
lean_ctor_set(v___x_3171_, 1, v_quotContext_3161_);
lean_ctor_set(v___x_3171_, 2, v_currMacroScope_3162_);
lean_ctor_set(v___x_3171_, 3, v_currRecDepth_3156_);
lean_ctor_set(v___x_3171_, 4, v_maxRecDepth_3157_);
lean_ctor_set(v___x_3171_, 5, v_ref_3158_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3173_, 0, v_nextMacroScope_3164_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
lean_ctor_set(v___x_3173_, 2, v___x_3172_);
v___x_3174_ = lean_apply_2(v_x_3144_, v___x_3171_, v___x_3173_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v_a_3176_; lean_object* v_macroScope_3177_; lean_object* v_traceMsgs_3178_; lean_object* v_expandedMacroDecls_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 1);
lean_inc(v_a_3175_);
v_a_3176_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3174_, 2);
v_macroScope_3177_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_macroScope_3177_);
v_traceMsgs_3178_ = lean_ctor_get(v_a_3175_, 1);
lean_inc(v_traceMsgs_3178_);
v_expandedMacroDecls_3179_ = lean_ctor_get(v_a_3175_, 2);
lean_inc(v_expandedMacroDecls_3179_);
lean_dec(v_a_3175_);
v___x_3180_ = lean_box(0);
v___x_3181_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_expandedMacroDecls_3179_, v___x_3180_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v_expandedMacroDecls_3179_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v___x_3182_; lean_object* v_env_3183_; lean_object* v_ngen_3184_; lean_object* v_auxDeclNGen_3185_; lean_object* v_traceState_3186_; lean_object* v_cache_3187_; lean_object* v_messages_3188_; lean_object* v_infoState_3189_; lean_object* v_snapshotTasks_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref_known(v___x_3181_, 1);
v___x_3182_ = lean_st_ref_take(v___y_3151_);
v_env_3183_ = lean_ctor_get(v___x_3182_, 0);
v_ngen_3184_ = lean_ctor_get(v___x_3182_, 2);
v_auxDeclNGen_3185_ = lean_ctor_get(v___x_3182_, 3);
v_traceState_3186_ = lean_ctor_get(v___x_3182_, 4);
v_cache_3187_ = lean_ctor_get(v___x_3182_, 5);
v_messages_3188_ = lean_ctor_get(v___x_3182_, 6);
v_infoState_3189_ = lean_ctor_get(v___x_3182_, 7);
v_snapshotTasks_3190_ = lean_ctor_get(v___x_3182_, 8);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v___x_3182_, 1);
lean_dec(v_unused_3217_);
v___x_3192_ = v___x_3182_;
v_isShared_3193_ = v_isSharedCheck_3216_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_snapshotTasks_3190_);
lean_inc(v_infoState_3189_);
lean_inc(v_messages_3188_);
lean_inc(v_cache_3187_);
lean_inc(v_traceState_3186_);
lean_inc(v_auxDeclNGen_3185_);
lean_inc(v_ngen_3184_);
lean_inc(v_env_3183_);
lean_dec(v___x_3182_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3216_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 1, v_macroScope_3177_);
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_env_3183_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_macroScope_3177_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_ngen_3184_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v_auxDeclNGen_3185_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v_traceState_3186_);
lean_ctor_set(v_reuseFailAlloc_3215_, 5, v_cache_3187_);
lean_ctor_set(v_reuseFailAlloc_3215_, 6, v_messages_3188_);
lean_ctor_set(v_reuseFailAlloc_3215_, 7, v_infoState_3189_);
lean_ctor_set(v_reuseFailAlloc_3215_, 8, v_snapshotTasks_3190_);
v___x_3195_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = lean_st_ref_set(v___y_3151_, v___x_3195_);
v___x_3197_ = l_List_reverse___redArg(v_traceMsgs_3178_);
v___x_3198_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15(v___x_3197_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3206_);
v___x_3200_ = v___x_3198_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_dec(v___x_3198_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v_a_3176_);
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3176_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_a_3176_);
v_a_3207_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3198_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3198_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v_traceMsgs_3178_);
lean_dec(v_macroScope_3177_);
lean_dec(v_a_3176_);
v_a_3218_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3181_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3181_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; 
v_a_3226_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3174_, 2);
if (lean_obj_tag(v_a_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v_a_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_a_3227_ = lean_ctor_get(v_a_3226_, 0);
lean_inc(v_a_3227_);
v_a_3228_ = lean_ctor_get(v_a_3226_, 1);
lean_inc_ref(v_a_3228_);
lean_dec_ref_known(v_a_3226_, 2);
v___x_3229_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___closed__0));
v___x_3230_ = lean_string_dec_eq(v_a_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3228_);
v___x_3232_ = l_Lean_MessageData_ofFormat(v___x_3231_);
v___x_3233_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_a_3227_, v___x_3232_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v_a_3227_);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; 
lean_dec_ref(v_a_3228_);
v___x_3234_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_a_3227_);
return v___x_3234_;
}
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg___boxed(lean_object* v_x_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(lean_object* v___x_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_quotContext_3250_; lean_object* v_currMacroScope_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_quotContext_3250_ = lean_ctor_get(v___y_3247_, 10);
lean_inc(v_quotContext_3250_);
v_currMacroScope_3251_ = lean_ctor_get(v___y_3247_, 11);
lean_inc(v_currMacroScope_3251_);
lean_dec_ref(v___y_3247_);
v___x_3252_ = l_Lean_addMacroScope(v_quotContext_3250_, v___x_3246_, v_currMacroScope_3251_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v___x_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___lam__0(v___x_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___f_3267_; lean_object* v___x_3268_; 
v___f_3267_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___closed__2));
v___x_3268_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3267_, v___y_3264_, v___y_3265_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg___boxed(lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_ref_3273_, uint8_t v_canonical_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3292_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = l_Lean_mkIdentFrom(v_ref_3273_, v_a_3284_, v_canonical_3274_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3288_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v_a_3293_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3283_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3283_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_ref_3301_, lean_object* v_canonical_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v_canonical_boxed_3311_; lean_object* v_res_3312_; 
v_canonical_boxed_3311_ = lean_unbox(v_canonical_3302_);
v_res_3312_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_ref_3301_, v_canonical_boxed_3311_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_ref_3301_);
return v_res_3312_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3325_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__15___closed__1));
v___x_3326_ = l_Lean_Name_append(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3329_ = l_Lean_stringToMessageData(v___x_3328_);
return v___x_3329_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3332_ = l_Lean_stringToMessageData(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__9));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3336_, lean_object* v_letOrReassign_3337_, lean_object* v_decl_3338_, lean_object* v_tk_3339_, lean_object* v_dec_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3336_, v_letOrReassign_3337_, v_decl_3338_, v_tk_3339_, v_dec_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3350_, lean_object* v_letOrReassign_3351_, lean_object* v_decl_3352_, lean_object* v_tk_3353_, lean_object* v_dec_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref_known(v___x_3363_, 1);
lean_inc(v_decl_3352_);
v___x_3364_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3352_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3351_, v_a_3365_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec_ref_known(v___x_3366_, 1);
v___x_3367_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3354_, v_tk_3353_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v___x_3369_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3351_, v_decl_3352_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v_doBlockResultType_3371_; lean_object* v___x_3372_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v_doBlockResultType_3371_ = lean_ctor_get(v_a_3355_, 3);
lean_inc_ref(v_doBlockResultType_3371_);
v___x_3372_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3371_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3591_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3591_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3591_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3377_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3378_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3380_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_a_3370_);
v___x_3381_ = l_Lean_Syntax_isOfKind(v_a_3370_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
lean_dec(v_a_3370_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_tk_3353_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v___x_3382_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3382_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3383_ = lean_unsigned_to_nat(0u);
v___x_3384_ = l_Lean_Syntax_getArg(v_a_3370_, v___x_3383_);
lean_dec(v_a_3370_);
v___x_3385_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__1));
lean_inc(v___x_3384_);
v___x_3386_ = l_Lean_Syntax_isOfKind(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
lean_dec(v_tk_3353_);
v___x_3387_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3384_);
v___x_3388_ = l_Lean_Syntax_isOfKind(v___x_3384_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; uint8_t v___x_3390_; 
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3384_);
v___x_3390_ = l_Lean_Syntax_isOfKind(v___x_3384_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec(v___x_3384_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v___x_3391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3391_;
}
else
{
lean_object* v___x_3392_; lean_object* v_id_3393_; lean_object* v_binders_3394_; lean_object* v_type_3395_; lean_object* v_value_3396_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; uint8_t v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; lean_object* v_id_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___x_3487_; 
v___x_3392_ = l_Lean_Elab_Term_mkLetIdDeclView(v___x_3384_);
lean_dec(v___x_3384_);
v_id_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_id_3393_);
v_binders_3394_ = lean_ctor_get(v___x_3392_, 1);
lean_inc_ref(v_binders_3394_);
v_type_3395_ = lean_ctor_get(v___x_3392_, 2);
lean_inc(v_type_3395_);
v_value_3396_ = lean_ctor_get(v___x_3392_, 3);
lean_inc(v_value_3396_);
lean_dec_ref(v___x_3392_);
v___x_3487_ = l_Lean_Syntax_isIdent(v_id_3393_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_id_3393_, v___x_3381_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
lean_dec(v_id_3393_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v_id_3469_ = v_a_3489_;
v___y_3470_ = v_a_3355_;
v___y_3471_ = v_a_3356_;
v___y_3472_ = v_a_3357_;
v___y_3473_ = v_a_3358_;
v___y_3474_ = v_a_3359_;
v___y_3475_ = v_a_3360_;
v___y_3476_ = v_a_3361_;
goto v___jp_3468_;
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_value_3396_);
lean_dec(v_type_3395_);
lean_dec_ref(v_binders_3394_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3490_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
v_id_3469_ = v_id_3393_;
v___y_3470_ = v_a_3355_;
v___y_3471_ = v_a_3356_;
v___y_3472_ = v_a_3357_;
v___y_3473_ = v_a_3358_;
v___y_3474_ = v_a_3359_;
v___y_3475_ = v_a_3360_;
v___y_3476_ = v_a_3361_;
goto v___jp_3468_;
}
v___jp_3397_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; 
v___x_3411_ = lean_box(v___x_3381_);
v___x_3412_ = lean_box(v___x_3386_);
v___x_3413_ = lean_box(v___y_3410_);
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3414_, 0, v_type_3395_);
lean_closure_set(v___f_3414_, 1, v_value_3396_);
lean_closure_set(v___f_3414_, 2, v___x_3411_);
lean_closure_set(v___f_3414_, 3, v___x_3412_);
lean_closure_set(v___f_3414_, 4, v___x_3383_);
lean_closure_set(v___f_3414_, 5, v___x_3413_);
v___x_3415_ = l_Lean_Elab_Term_elabBindersEx___redArg(v_binders_3394_, v___f_3414_, v___y_3403_, v___y_3405_, v___y_3402_, v___y_3409_, v___y_3407_, v___y_3404_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v_options_3417_; lean_object* v_fst_3418_; lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3459_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v_options_3417_ = lean_ctor_get(v___y_3407_, 2);
v_fst_3418_ = lean_ctor_get(v_a_3416_, 0);
v_snd_3419_ = lean_ctor_get(v_a_3416_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3421_ = v_a_3416_;
v_isShared_3422_ = v_isSharedCheck_3459_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_inc(v_fst_3418_);
lean_dec(v_a_3416_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3459_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_inheritedTraceOptions_3423_; uint8_t v_hasTrace_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___f_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v_inheritedTraceOptions_3423_ = lean_ctor_get(v___y_3407_, 13);
v_hasTrace_3424_ = lean_ctor_get_uint8(v_options_3417_, sizeof(void*)*1);
v___x_3425_ = lean_box(v___y_3399_);
v___x_3426_ = lean_box(v___y_3401_);
v___x_3427_ = lean_box(v___x_3386_);
v___x_3428_ = lean_box(v___y_3410_);
v___x_3429_ = lean_box(v___x_3381_);
lean_inc(v_snd_3419_);
v___f_3430_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 20, 11);
lean_closure_set(v___f_3430_, 0, v___y_3400_);
lean_closure_set(v___f_3430_, 1, v___y_3398_);
lean_closure_set(v___f_3430_, 2, v_a_3368_);
lean_closure_set(v___f_3430_, 3, v___x_3425_);
lean_closure_set(v___f_3430_, 4, v___x_3426_);
lean_closure_set(v___f_3430_, 5, v___x_3427_);
lean_closure_set(v___f_3430_, 6, v_snd_3419_);
lean_closure_set(v___f_3430_, 7, v___x_3428_);
lean_closure_set(v___f_3430_, 8, v___x_3429_);
lean_closure_set(v___f_3430_, 9, v_letOrReassign_3351_);
lean_closure_set(v___f_3430_, 10, v_a_3365_);
v___x_3431_ = l_Lean_Syntax_getId(v___y_3406_);
lean_dec(v___y_3406_);
v___x_3432_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3431_);
if (v_hasTrace_3424_ == 0)
{
lean_object* v___x_3433_; 
lean_del_object(v___x_3421_);
v___x_3433_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3431_, v_fst_3418_, v_snd_3419_, v___f_3430_, v___y_3410_, v___x_3432_, v___y_3408_, v___y_3403_, v___y_3405_, v___y_3402_, v___y_3409_, v___y_3407_, v___y_3404_);
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3434_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3435_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3423_, v_options_3417_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_del_object(v___x_3421_);
v___x_3437_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3431_, v_fst_3418_, v_snd_3419_, v___f_3430_, v___y_3410_, v___x_3432_, v___y_3408_, v___y_3403_, v___y_3405_, v___y_3402_, v___y_3409_, v___y_3407_, v___y_3404_);
return v___x_3437_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; 
lean_inc(v___x_3431_);
v___x_3438_ = l_Lean_MessageData_ofName(v___x_3431_);
v___x_3439_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 7);
lean_ctor_set(v___x_3421_, 1, v___x_3439_);
lean_ctor_set(v___x_3421_, 0, v___x_3438_);
v___x_3441_ = v___x_3421_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_inc(v_fst_3418_);
v___x_3442_ = l_Lean_MessageData_ofExpr(v_fst_3418_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
lean_inc(v_snd_3419_);
v___x_3446_ = l_Lean_MessageData_ofExpr(v_snd_3419_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v___x_3434_, v___x_3447_, v___y_3402_, v___y_3409_, v___y_3407_, v___y_3404_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v___x_3449_; 
lean_dec_ref_known(v___x_3448_, 1);
v___x_3449_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3431_, v_fst_3418_, v_snd_3419_, v___f_3430_, v___y_3410_, v___x_3432_, v___y_3408_, v___y_3403_, v___y_3405_, v___y_3402_, v___y_3409_, v___y_3407_, v___y_3404_);
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v___x_3431_);
lean_dec_ref(v___f_3430_);
lean_dec(v_snd_3419_);
lean_dec(v_fst_3418_);
v_a_3450_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3448_);
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
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v___y_3406_);
lean_dec(v___y_3400_);
lean_dec(v___y_3398_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
v_a_3460_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3415_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3415_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
v___jp_3468_:
{
uint8_t v_nondep_3477_; 
v_nondep_3477_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1);
if (v_nondep_3477_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3351_) == 1)
{
uint8_t v_usedOnly_3478_; uint8_t v_zeta_3479_; lean_object* v_eq_x3f_3480_; 
v_usedOnly_3478_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 1);
v_zeta_3479_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 2);
v_eq_x3f_3480_ = lean_ctor_get(v_config_3350_, 0);
lean_inc(v_eq_x3f_3480_);
lean_dec_ref(v_config_3350_);
lean_inc(v_id_3469_);
v___y_3398_ = v_eq_x3f_3480_;
v___y_3399_ = v_zeta_3479_;
v___y_3400_ = v_id_3469_;
v___y_3401_ = v_usedOnly_3478_;
v___y_3402_ = v___y_3473_;
v___y_3403_ = v___y_3471_;
v___y_3404_ = v___y_3476_;
v___y_3405_ = v___y_3472_;
v___y_3406_ = v_id_3469_;
v___y_3407_ = v___y_3475_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v___x_3381_;
goto v___jp_3397_;
}
else
{
uint8_t v_usedOnly_3481_; uint8_t v_zeta_3482_; lean_object* v_eq_x3f_3483_; 
v_usedOnly_3481_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 1);
v_zeta_3482_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 2);
v_eq_x3f_3483_ = lean_ctor_get(v_config_3350_, 0);
lean_inc(v_eq_x3f_3483_);
lean_dec_ref(v_config_3350_);
lean_inc(v_id_3469_);
v___y_3398_ = v_eq_x3f_3483_;
v___y_3399_ = v_zeta_3482_;
v___y_3400_ = v_id_3469_;
v___y_3401_ = v_usedOnly_3481_;
v___y_3402_ = v___y_3473_;
v___y_3403_ = v___y_3471_;
v___y_3404_ = v___y_3476_;
v___y_3405_ = v___y_3472_;
v___y_3406_ = v_id_3469_;
v___y_3407_ = v___y_3475_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v_nondep_3477_;
goto v___jp_3397_;
}
}
else
{
uint8_t v_usedOnly_3484_; uint8_t v_zeta_3485_; lean_object* v_eq_x3f_3486_; 
v_usedOnly_3484_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 1);
v_zeta_3485_ = lean_ctor_get_uint8(v_config_3350_, sizeof(void*)*1 + 2);
v_eq_x3f_3486_ = lean_ctor_get(v_config_3350_, 0);
lean_inc(v_eq_x3f_3486_);
lean_dec_ref(v_config_3350_);
lean_inc(v_id_3469_);
v___y_3398_ = v_eq_x3f_3486_;
v___y_3399_ = v_zeta_3485_;
v___y_3400_ = v_id_3469_;
v___y_3401_ = v_usedOnly_3484_;
v___y_3402_ = v___y_3473_;
v___y_3403_ = v___y_3471_;
v___y_3404_ = v___y_3476_;
v___y_3405_ = v___y_3472_;
v___y_3406_ = v_id_3469_;
v___y_3407_ = v___y_3475_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v___x_3381_;
goto v___jp_3397_;
}
}
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3499_ = l_Lean_Syntax_getArg(v___x_3384_, v___x_3498_);
v___x_3500_ = l_Lean_Syntax_matchesNull(v___x_3499_, v___x_3383_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v___x_3384_);
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; lean_object* v_rhs_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v_xType_x3f_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3502_ = lean_box(v___x_3386_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 10, 1);
lean_closure_set(v___f_3503_, 0, v___x_3502_);
v___x_3504_ = l_Lean_Syntax_getArg(v___x_3384_, v___x_3383_);
v___x_3559_ = lean_unsigned_to_nat(2u);
v___x_3560_ = l_Lean_Syntax_getArg(v___x_3384_, v___x_3559_);
v___x_3561_ = l_Lean_Syntax_isNone(v___x_3560_);
if (v___x_3561_ == 0)
{
uint8_t v___x_3562_; 
lean_inc(v___x_3560_);
v___x_3562_ = l_Lean_Syntax_matchesNull(v___x_3560_, v___x_3498_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
lean_dec(v___x_3560_);
lean_dec(v___x_3504_);
lean_dec_ref(v___f_3503_);
lean_dec(v___x_3384_);
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v___x_3563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3563_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3564_ = l_Lean_Syntax_getArg(v___x_3560_, v___x_3383_);
lean_dec(v___x_3560_);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3564_);
v___x_3566_ = l_Lean_Syntax_isOfKind(v___x_3564_, v___x_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec(v___x_3564_);
lean_dec(v___x_3504_);
lean_dec_ref(v___f_3503_);
lean_dec(v___x_3384_);
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v___x_3567_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_3567_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = l_Lean_Syntax_getArg(v___x_3564_, v___x_3498_);
lean_dec(v___x_3564_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 1);
lean_ctor_set(v___x_3375_, 0, v___x_3568_);
v___x_3570_ = v___x_3375_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
v_xType_x3f_3525_ = v___x_3570_;
v___y_3526_ = v_a_3355_;
v___y_3527_ = v_a_3356_;
v___y_3528_ = v_a_3357_;
v___y_3529_ = v_a_3358_;
v___y_3530_ = v_a_3359_;
v___y_3531_ = v_a_3360_;
v___y_3532_ = v_a_3361_;
goto v___jp_3524_;
}
}
}
}
else
{
lean_object* v___x_3572_; 
lean_dec(v___x_3560_);
lean_del_object(v___x_3375_);
v___x_3572_ = lean_box(0);
v_xType_x3f_3525_ = v___x_3572_;
v___y_3526_ = v_a_3355_;
v___y_3527_ = v_a_3356_;
v___y_3528_ = v_a_3357_;
v___y_3529_ = v_a_3358_;
v___y_3530_ = v_a_3359_;
v___y_3531_ = v_a_3360_;
v___y_3532_ = v_a_3361_;
goto v___jp_3524_;
}
v___jp_3505_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3514_ = lean_box(v___x_3386_);
v___x_3515_ = lean_box(v___x_3381_);
lean_inc(v___x_3504_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___boxed), 19, 10);
lean_closure_set(v___f_3516_, 0, v_rhs_3506_);
lean_closure_set(v___f_3516_, 1, v___x_3514_);
lean_closure_set(v___f_3516_, 2, v_config_3350_);
lean_closure_set(v___f_3516_, 3, v_a_3373_);
lean_closure_set(v___f_3516_, 4, v___x_3515_);
lean_closure_set(v___f_3516_, 5, v___x_3377_);
lean_closure_set(v___f_3516_, 6, v___x_3378_);
lean_closure_set(v___f_3516_, 7, v___x_3379_);
lean_closure_set(v___f_3516_, 8, v___f_3503_);
lean_closure_set(v___f_3516_, 9, v___x_3504_);
v___x_3517_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3517_, 0, v_a_3368_);
v___x_3518_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3518_, 0, v_letOrReassign_3351_);
lean_closure_set(v___x_3518_, 1, v_a_3365_);
lean_closure_set(v___x_3518_, 2, v___x_3517_);
v___x_3519_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__10);
v___x_3520_ = l_Lean_MessageData_ofSyntax(v___x_3504_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_box(0);
v___x_3523_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3521_, v___x_3518_, v___f_3516_, v___x_3522_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
return v___x_3523_;
}
v___jp_3524_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_unsigned_to_nat(4u);
v___x_3534_ = l_Lean_Syntax_getArg(v___x_3384_, v___x_3533_);
lean_dec(v___x_3384_);
if (lean_obj_tag(v_xType_x3f_3525_) == 0)
{
v_rhs_3506_ = v___x_3534_;
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3527_;
v___y_3509_ = v___y_3528_;
v___y_3510_ = v___y_3529_;
v___y_3511_ = v___y_3530_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3532_;
goto v___jp_3505_;
}
else
{
lean_object* v_val_3535_; lean_object* v_ref_3536_; lean_object* v_quotContext_3537_; lean_object* v_currMacroScope_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_val_3535_ = lean_ctor_get(v_xType_x3f_3525_, 0);
lean_inc(v_val_3535_);
lean_dec_ref_known(v_xType_x3f_3525_, 1);
v_ref_3536_ = lean_ctor_get(v___y_3531_, 5);
v_quotContext_3537_ = lean_ctor_get(v___y_3531_, 10);
v_currMacroScope_3538_ = lean_ctor_get(v___y_3531_, 11);
v___x_3539_ = l_Lean_SourceInfo_fromRef(v_ref_3536_, v___x_3386_);
v___x_3540_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_3539_, 7);
v___x_3543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3539_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3545_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3546_ = lean_box(0);
lean_inc(v_currMacroScope_3538_);
lean_inc(v_quotContext_3537_);
v___x_3547_ = l_Lean_addMacroScope(v_quotContext_3537_, v___x_3546_, v_currMacroScope_3538_);
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_3549_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3539_);
lean_ctor_set(v___x_3549_, 1, v___x_3545_);
lean_ctor_set(v___x_3549_, 2, v___x_3547_);
lean_ctor_set(v___x_3549_, 3, v___x_3548_);
v___x_3550_ = l_Lean_Syntax_node1(v___x_3539_, v___x_3544_, v___x_3549_);
v___x_3551_ = l_Lean_Syntax_node2(v___x_3539_, v___x_3541_, v___x_3543_, v___x_3550_);
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3539_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3555_ = l_Lean_Syntax_node1(v___x_3539_, v___x_3554_, v_val_3535_);
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3539_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_Syntax_node5(v___x_3539_, v___x_3540_, v___x_3551_, v___x_3534_, v___x_3553_, v___x_3555_, v___x_3557_);
v_rhs_3506_ = v___x_3558_;
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3527_;
v___y_3509_ = v___y_3528_;
v___y_3510_ = v___y_3529_;
v___y_3511_ = v___y_3530_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3532_;
goto v___jp_3505_;
}
}
}
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_del_object(v___x_3375_);
lean_dec(v_a_3373_);
lean_dec(v_a_3365_);
v___x_3573_ = lean_box(v___x_3381_);
lean_inc(v___x_3384_);
v___x_3574_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3574_, 0, v___x_3384_);
lean_closure_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v___x_3574_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v_ref_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v_ref_3577_ = lean_ctor_get(v_a_3360_, 5);
v___x_3578_ = 0;
v___x_3579_ = l_Lean_SourceInfo_fromRef(v_ref_3577_, v___x_3578_);
v___x_3580_ = l_Lean_Syntax_node1(v___x_3579_, v___x_3380_, v_a_3576_);
lean_inc(v___x_3580_);
v___x_3581_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3581_, 0, v_config_3350_);
lean_closure_set(v___x_3581_, 1, v_letOrReassign_3351_);
lean_closure_set(v___x_3581_, 2, v___x_3580_);
lean_closure_set(v___x_3581_, 3, v_tk_3353_);
lean_closure_set(v___x_3581_, 4, v_a_3368_);
v___x_3582_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3384_, v___x_3580_, v___x_3581_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
return v___x_3582_;
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___x_3384_);
lean_dec(v_a_3368_);
lean_dec(v_tk_3353_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3583_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3575_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3575_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3370_);
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_tk_3353_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
return v___x_3372_;
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v_a_3368_);
lean_dec(v_a_3365_);
lean_dec(v_tk_3353_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3592_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3369_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3369_);
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
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_a_3365_);
lean_dec(v_tk_3353_);
lean_dec(v_decl_3352_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3600_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3367_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3367_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v_a_3365_);
lean_dec_ref(v_dec_3354_);
lean_dec(v_tk_3353_);
lean_dec(v_decl_3352_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3608_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3366_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3366_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v_dec_3354_);
lean_dec(v_tk_3353_);
lean_dec(v_decl_3352_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3616_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3364_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3364_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_dec_3354_);
lean_dec(v_tk_3353_);
lean_dec(v_decl_3352_);
lean_dec(v_letOrReassign_3351_);
lean_dec_ref(v_config_3350_);
v_a_3624_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3363_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3363_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3633_, v_x_3634_, v_x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_cls_3637_, lean_object* v_msg_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___redArg(v_cls_3637_, v_msg_3638_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_cls_3648_, lean_object* v_msg_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_cls_3648_, v_msg_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___redArg(v___y_3664_, v___y_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8___boxed(lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__8(v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_3677_, lean_object* v_beforeStx_3678_, lean_object* v_afterStx_3679_, lean_object* v_x_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_beforeStx_3678_, v_afterStx_3679_, v_x_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_3690_, lean_object* v_beforeStx_3691_, lean_object* v_afterStx_3692_, lean_object* v_x_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_3690_, v_beforeStx_3691_, v_afterStx_3692_, v_x_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(lean_object* v_00_u03b1_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___redArg(v_x_3704_, v___y_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_x_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__12(v_00_u03b1_3708_, v_x_3709_, v___y_3710_, v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v_x_3709_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(lean_object* v_00_u03b1_3713_, lean_object* v_ref_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___redArg(v_ref_3714_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17___boxed(lean_object* v_00_u03b1_3724_, lean_object* v_ref_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__17(v_00_u03b1_3724_, v_ref_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(lean_object* v_00_u03b1_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___redArg(v_x_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9___boxed(lean_object* v_00_u03b1_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9(v_00_u03b1_3746_, v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_3757_, lean_object* v_x_3758_, size_t v_x_3759_, size_t v_x_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_3758_, v_x_3759_, v_x_3760_, v_x_3761_, v_x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3764_, lean_object* v_x_3765_, lean_object* v_x_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
size_t v_x_102784__boxed_3770_; size_t v_x_102785__boxed_3771_; lean_object* v_res_3772_; 
v_x_102784__boxed_3770_ = lean_unbox_usize(v_x_3766_);
lean_dec(v_x_3766_);
v_x_102785__boxed_3771_ = lean_unbox_usize(v_x_3767_);
lean_dec(v_x_3767_);
v_res_3772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_3764_, v_x_3765_, v_x_102784__boxed_3770_, v_x_102785__boxed_3771_, v_x_3768_, v_x_3769_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(lean_object* v_00_u03b1_3773_, lean_object* v_stx_3774_, lean_object* v_output_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___redArg(v_stx_3774_, v_output_3775_, v_x_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3785_, lean_object* v_stx_3786_, lean_object* v_output_3787_, lean_object* v_x_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10(v_00_u03b1_3785_, v_stx_3786_, v_output_3787_, v_x_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(lean_object* v_as_3797_, lean_object* v_as_x27_3798_, lean_object* v_b_3799_, lean_object* v_a_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___redArg(v_as_x27_3798_, v_b_3799_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14___boxed(lean_object* v_as_3810_, lean_object* v_as_x27_3811_, lean_object* v_b_3812_, lean_object* v_a_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__14(v_as_3810_, v_as_x27_3811_, v_b_3812_, v_a_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v_as_x27_3811_);
lean_dec(v_as_3810_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(lean_object* v_00_u03b1_3823_, lean_object* v_ref_3824_, lean_object* v_msg_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_ref_3824_, v_msg_3825_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___boxed(lean_object* v_00_u03b1_3835_, lean_object* v_ref_3836_, lean_object* v_msg_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16(v_00_u03b1_3835_, v_ref_3836_, v_msg_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v_ref_3836_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3847_, lean_object* v_n_3848_, lean_object* v_k_3849_, lean_object* v_v_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_n_3848_, v_k_3849_, v_v_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3852_, size_t v_depth_3853_, lean_object* v_keys_3854_, lean_object* v_vals_3855_, lean_object* v_heq_3856_, lean_object* v_i_3857_, lean_object* v_entries_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___redArg(v_depth_3853_, v_keys_3854_, v_vals_3855_, v_i_3857_, v_entries_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_3860_, lean_object* v_depth_3861_, lean_object* v_keys_3862_, lean_object* v_vals_3863_, lean_object* v_heq_3864_, lean_object* v_i_3865_, lean_object* v_entries_3866_){
_start:
{
size_t v_depth_boxed_3867_; lean_object* v_res_3868_; 
v_depth_boxed_3867_ = lean_unbox_usize(v_depth_3861_);
lean_dec(v_depth_3861_);
v_res_3868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__5(v_00_u03b2_3860_, v_depth_boxed_3867_, v_keys_3862_, v_vals_3863_, v_heq_3864_, v_i_3865_, v_entries_3866_);
lean_dec_ref(v_vals_3863_);
lean_dec_ref(v_keys_3862_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___redArg(v___y_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18___boxed(lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13_spec__18(v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(lean_object* v_00_u03b1_3885_, lean_object* v_x_3886_, lean_object* v_mkInfoTree_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___redArg(v_x_3886_, v_mkInfoTree_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3896_, lean_object* v_x_3897_, lean_object* v_mkInfoTree_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__10_spec__13(v_00_u03b1_3896_, v_x_3897_, v_mkInfoTree_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(lean_object* v_00_u03b2_3907_, lean_object* v_m_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___redArg(v_m_3908_, v_a_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3911_, lean_object* v_m_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19(v_00_u03b2_3911_, v_m_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_m_3912_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14(lean_object* v_00_u03b2_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4_spec__14___redArg(v_x_3916_, v_x_3917_, v_x_3918_, v_x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(lean_object* v_00_u03b2_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_){
_start:
{
uint8_t v___x_3924_; 
v___x_3924_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___redArg(v_x_3922_, v_x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3925_, lean_object* v_x_3926_, lean_object* v_x_3927_){
_start:
{
uint8_t v_res_3928_; lean_object* v_r_3929_; 
v_res_3928_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21(v_00_u03b2_3925_, v_x_3926_, v_x_3927_);
lean_dec_ref(v_x_3927_);
lean_dec_ref(v_x_3926_);
v_r_3929_ = lean_box(v_res_3928_);
return v_r_3929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(lean_object* v_00_u03b2_3930_, lean_object* v_a_3931_, lean_object* v_x_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___redArg(v_a_3931_, v_x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24___boxed(lean_object* v_00_u03b2_3934_, lean_object* v_a_3935_, lean_object* v_x_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__19_spec__24(v_00_u03b2_3934_, v_a_3935_, v_x_3936_);
lean_dec(v_x_3936_);
lean_dec(v_a_3935_);
return v_res_3937_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(lean_object* v_00_u03b2_3938_, lean_object* v_x_3939_, size_t v_x_3940_, lean_object* v_x_3941_){
_start:
{
uint8_t v___x_3942_; 
v___x_3942_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___redArg(v_x_3939_, v_x_3940_, v_x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25___boxed(lean_object* v_00_u03b2_3943_, lean_object* v_x_3944_, lean_object* v_x_3945_, lean_object* v_x_3946_){
_start:
{
size_t v_x_102954__boxed_3947_; uint8_t v_res_3948_; lean_object* v_r_3949_; 
v_x_102954__boxed_3947_ = lean_unbox_usize(v_x_3945_);
lean_dec(v_x_3945_);
v_res_3948_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25(v_00_u03b2_3943_, v_x_3944_, v_x_102954__boxed_3947_, v_x_3946_);
lean_dec_ref(v_x_3946_);
lean_dec_ref(v_x_3944_);
v_r_3949_ = lean_box(v_res_3948_);
return v_r_3949_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(lean_object* v_00_u03b2_3950_, lean_object* v_keys_3951_, lean_object* v_vals_3952_, lean_object* v_heq_3953_, lean_object* v_i_3954_, lean_object* v_k_3955_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___redArg(v_keys_3951_, v_i_3954_, v_k_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28___boxed(lean_object* v_00_u03b2_3957_, lean_object* v_keys_3958_, lean_object* v_vals_3959_, lean_object* v_heq_3960_, lean_object* v_i_3961_, lean_object* v_k_3962_){
_start:
{
uint8_t v_res_3963_; lean_object* v_r_3964_; 
v_res_3963_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__13_spec__17_spec__21_spec__25_spec__28(v_00_u03b2_3957_, v_keys_3958_, v_vals_3959_, v_heq_3960_, v_i_3961_, v_k_3962_);
lean_dec_ref(v_k_3962_);
lean_dec_ref(v_vals_3959_);
lean_dec_ref(v_keys_3958_);
v_r_3964_ = lean_box(v_res_3963_);
return v_r_3964_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__1));
v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0(lean_object* v_letOrReassign_3974_, lean_object* v_otherwise_x3f_3975_, uint8_t v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v_dec_3982_, uint8_t v___x_3983_, lean_object* v___y_3984_, lean_object* v___x_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4017_; 
switch(lean_obj_tag(v_letOrReassign_3974_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_3975_) == 1)
{
lean_object* v_mutTk_x3f_4028_; lean_object* v_val_4029_; lean_object* v_ref_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4060_; 
v_mutTk_x3f_4028_ = lean_ctor_get(v_letOrReassign_3974_, 0);
v_val_4029_ = lean_ctor_get(v_otherwise_x3f_3975_, 0);
lean_inc(v_val_4029_);
lean_dec_ref_known(v_otherwise_x3f_3975_, 1);
v_ref_4030_ = lean_ctor_get(v___y_3991_, 5);
v___x_4031_ = l_Lean_SourceInfo_fromRef(v_ref_4030_, v___x_3976_);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_3979_);
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
v___x_4033_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4032_);
v___x_4034_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4031_);
v___x_4035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4031_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4037_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4028_) == 1)
{
lean_object* v_val_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_val_4075_ = lean_ctor_get(v_mutTk_x3f_4028_, 0);
v___x_4076_ = l_Lean_SourceInfo_fromRef(v_val_4075_, v___x_3983_);
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = l_Array_mkArray1___redArg(v___x_4078_);
v___y_4060_ = v___x_4079_;
goto v___jp_4059_;
}
else
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_mk_empty_array_with_capacity(v___x_3985_);
v___y_4060_ = v___x_4080_;
goto v___jp_4059_;
}
v___jp_4038_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4044_ = l_Array_append___redArg(v___x_4037_, v___y_4043_);
lean_dec_ref(v___y_4043_);
lean_inc(v___x_4031_);
v___x_4045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4031_);
lean_ctor_set(v___x_4045_, 1, v___x_4036_);
lean_ctor_set(v___x_4045_, 2, v___x_4044_);
v___x_4046_ = lean_unsigned_to_nat(9u);
v___x_4047_ = lean_mk_empty_array_with_capacity(v___x_4046_);
v___x_4048_ = lean_array_push(v___x_4047_, v___x_4035_);
v___x_4049_ = lean_array_push(v___x_4048_, v___y_4041_);
v___x_4050_ = lean_array_push(v___x_4049_, v___y_4040_);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_3980_);
v___x_4052_ = lean_array_push(v___x_4051_, v___y_4039_);
v___x_4053_ = lean_array_push(v___x_4052_, v___x_3981_);
v___x_4054_ = lean_array_push(v___x_4053_, v___y_4042_);
v___x_4055_ = lean_array_push(v___x_4054_, v_val_4029_);
v___x_4056_ = lean_array_push(v___x_4055_, v___x_4045_);
v___x_4057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4031_);
lean_ctor_set(v___x_4057_, 1, v___x_4033_);
lean_ctor_set(v___x_4057_, 2, v___x_4056_);
v___x_4058_ = l_Lean_Elab_Do_elabDoElem(v___x_4057_, v_dec_3982_, v___x_3983_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_4058_;
}
v___jp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4061_ = l_Array_append___redArg(v___x_4037_, v___y_4060_);
lean_dec_ref(v___y_4060_);
lean_inc_n(v___x_4031_, 5);
v___x_4062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4031_);
lean_ctor_set(v___x_4062_, 1, v___x_4036_);
lean_ctor_set(v___x_4062_, 2, v___x_4061_);
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4064_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4063_);
v___x_4065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4031_);
lean_ctor_set(v___x_4065_, 1, v___x_4036_);
lean_ctor_set(v___x_4065_, 2, v___x_4037_);
v___x_4066_ = l_Lean_Syntax_node1(v___x_4031_, v___x_4064_, v___x_4065_);
v___x_4067_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4031_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4031_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
if (lean_obj_tag(v___y_3984_) == 0)
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_mk_empty_array_with_capacity(v___x_3985_);
v___y_4039_ = v___x_4068_;
v___y_4040_ = v___x_4066_;
v___y_4041_ = v___x_4062_;
v___y_4042_ = v___x_4070_;
v___y_4043_ = v___x_4071_;
goto v___jp_4038_;
}
else
{
lean_object* v_val_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_val_4072_ = lean_ctor_get(v___y_3984_, 0);
lean_inc(v_val_4072_);
lean_dec_ref_known(v___y_3984_, 1);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_3985_);
v___x_4074_ = lean_array_push(v___x_4073_, v_val_4072_);
v___y_4039_ = v___x_4068_;
v___y_4040_ = v___x_4066_;
v___y_4041_ = v___x_4062_;
v___y_4042_ = v___x_4070_;
v___y_4043_ = v___x_4074_;
goto v___jp_4038_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4081_; lean_object* v_ref_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___y_4091_; 
lean_dec(v___y_3984_);
lean_dec(v_otherwise_x3f_3975_);
v_mutTk_x3f_4081_ = lean_ctor_get(v_letOrReassign_3974_, 0);
v_ref_4082_ = lean_ctor_get(v___y_3991_, 5);
v___x_4083_ = l_Lean_SourceInfo_fromRef(v_ref_4082_, v___x_3976_);
v___x_4084_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_3979_);
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
v___x_4085_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4084_);
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4083_);
v___x_4087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4083_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4089_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4081_) == 1)
{
lean_object* v_val_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v_val_4108_ = lean_ctor_get(v_mutTk_x3f_4081_, 0);
v___x_4109_ = l_Lean_SourceInfo_fromRef(v_val_4108_, v___x_3983_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4109_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = l_Array_mkArray1___redArg(v___x_4111_);
v___y_4091_ = v___x_4112_;
goto v___jp_4090_;
}
else
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_mk_empty_array_with_capacity(v___x_3985_);
v___y_4091_ = v___x_4113_;
goto v___jp_4090_;
}
v___jp_4090_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4092_ = l_Array_append___redArg(v___x_4089_, v___y_4091_);
lean_dec_ref(v___y_4091_);
lean_inc_n(v___x_4083_, 6);
v___x_4093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4083_);
lean_ctor_set(v___x_4093_, 1, v___x_4088_);
lean_ctor_set(v___x_4093_, 2, v___x_4092_);
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_3979_, 2);
lean_inc_ref_n(v___x_3978_, 2);
lean_inc_ref_n(v___x_3977_, 2);
v___x_4095_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4094_);
v___x_4096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4083_);
lean_ctor_set(v___x_4096_, 1, v___x_4088_);
lean_ctor_set(v___x_4096_, 2, v___x_4089_);
lean_inc_ref_n(v___x_4096_, 2);
v___x_4097_ = l_Lean_Syntax_node1(v___x_4083_, v___x_4095_, v___x_4096_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4099_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4098_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4101_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4100_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4083_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_Syntax_node5(v___x_4083_, v___x_4101_, v___x_3980_, v___x_4096_, v___x_4096_, v___x_4103_, v___x_3981_);
v___x_4105_ = l_Lean_Syntax_node1(v___x_4083_, v___x_4099_, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_node4(v___x_4083_, v___x_4085_, v___x_4087_, v___x_4093_, v___x_4097_, v___x_4105_);
v___x_4107_ = l_Lean_Elab_Do_elabDoElem(v___x_4106_, v_dec_3982_, v___x_3983_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_4107_;
}
}
}
case 1:
{
lean_dec(v___y_3984_);
if (lean_obj_tag(v_otherwise_x3f_3975_) == 1)
{
lean_object* v___x_4114_; 
lean_dec_ref_known(v_otherwise_x3f_3975_, 1);
lean_dec_ref(v_dec_3982_);
lean_dec(v___x_3981_);
lean_dec(v___x_3980_);
lean_dec_ref(v___x_3979_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v___x_3977_);
v___x_4114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4114_;
}
else
{
lean_object* v_ref_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec(v_otherwise_x3f_3975_);
v_ref_4115_ = lean_ctor_get(v___y_3991_, 5);
v___x_4116_ = l_Lean_SourceInfo_fromRef(v_ref_4115_, v___x_3976_);
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_3979_, 3);
lean_inc_ref_n(v___x_3978_, 3);
lean_inc_ref_n(v___x_3977_, 3);
v___x_4118_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4116_, 6);
v___x_4120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4116_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4122_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4121_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4124_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4116_);
lean_ctor_set(v___x_4125_, 1, v___x_4123_);
lean_ctor_set(v___x_4125_, 2, v___x_4124_);
lean_inc_ref_n(v___x_4125_, 2);
v___x_4126_ = l_Lean_Syntax_node1(v___x_4116_, v___x_4122_, v___x_4125_);
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4128_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4127_);
v___x_4129_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4130_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4129_);
v___x_4131_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4116_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Lean_Syntax_node5(v___x_4116_, v___x_4130_, v___x_3980_, v___x_4125_, v___x_4125_, v___x_4132_, v___x_3981_);
v___x_4134_ = l_Lean_Syntax_node1(v___x_4116_, v___x_4128_, v___x_4133_);
v___x_4135_ = l_Lean_Syntax_node3(v___x_4116_, v___x_4118_, v___x_4120_, v___x_4126_, v___x_4134_);
v___x_4136_ = l_Lean_Elab_Do_elabDoElem(v___x_4135_, v_dec_3982_, v___x_3983_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_4136_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_3975_);
if (lean_obj_tag(v___y_3984_) == 0)
{
v___y_4017_ = v___x_3983_;
goto v___jp_4016_;
}
else
{
lean_dec_ref_known(v___y_3984_, 1);
v___y_4017_ = v___x_3976_;
goto v___jp_4016_;
}
}
}
v___jp_3994_:
{
lean_object* v_ref_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_ref_4002_ = lean_ctor_get(v___y_4000_, 5);
v___x_4003_ = l_Lean_SourceInfo_fromRef(v_ref_4002_, v___x_3976_);
v___x_4004_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_3979_);
lean_inc_ref(v___x_3978_);
lean_inc_ref(v___x_3977_);
v___x_4005_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4004_);
v___x_4006_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4007_ = l_Lean_Name_mkStr4(v___x_3977_, v___x_3978_, v___x_3979_, v___x_4006_);
v___x_4008_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4009_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4003_, 3);
v___x_4010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4003_);
lean_ctor_set(v___x_4010_, 1, v___x_4008_);
lean_ctor_set(v___x_4010_, 2, v___x_4009_);
v___x_4011_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4003_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
lean_inc_ref(v___x_4010_);
v___x_4013_ = l_Lean_Syntax_node5(v___x_4003_, v___x_4007_, v___x_3980_, v___x_4010_, v___x_4010_, v___x_4012_, v___x_3981_);
v___x_4014_ = l_Lean_Syntax_node1(v___x_4003_, v___x_4005_, v___x_4013_);
v___x_4015_ = l_Lean_Elab_Do_elabDoElem(v___x_4014_, v_dec_3982_, v___x_3983_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
return v___x_4015_;
}
v___jp_4016_:
{
if (v___y_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v_dec_3982_);
lean_dec(v___x_3981_);
lean_dec(v___x_3980_);
lean_dec_ref(v___x_3979_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v___x_3977_);
v___x_4018_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4019_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4018_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
v___y_3995_ = v___y_3986_;
v___y_3996_ = v___y_3987_;
v___y_3997_ = v___y_3988_;
v___y_3998_ = v___y_3989_;
v___y_3999_ = v___y_3990_;
v___y_4000_ = v___y_3991_;
v___y_4001_ = v___y_3992_;
goto v___jp_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__0___boxed(lean_object** _args){
lean_object* v_letOrReassign_4137_ = _args[0];
lean_object* v_otherwise_x3f_4138_ = _args[1];
lean_object* v___x_4139_ = _args[2];
lean_object* v___x_4140_ = _args[3];
lean_object* v___x_4141_ = _args[4];
lean_object* v___x_4142_ = _args[5];
lean_object* v___x_4143_ = _args[6];
lean_object* v___x_4144_ = _args[7];
lean_object* v_dec_4145_ = _args[8];
lean_object* v___x_4146_ = _args[9];
lean_object* v___y_4147_ = _args[10];
lean_object* v___x_4148_ = _args[11];
lean_object* v___y_4149_ = _args[12];
lean_object* v___y_4150_ = _args[13];
lean_object* v___y_4151_ = _args[14];
lean_object* v___y_4152_ = _args[15];
lean_object* v___y_4153_ = _args[16];
lean_object* v___y_4154_ = _args[17];
lean_object* v___y_4155_ = _args[18];
lean_object* v___y_4156_ = _args[19];
_start:
{
uint8_t v___x_39001__boxed_4157_; uint8_t v___x_39007__boxed_4158_; lean_object* v_res_4159_; 
v___x_39001__boxed_4157_ = lean_unbox(v___x_4139_);
v___x_39007__boxed_4158_ = lean_unbox(v___x_4146_);
v_res_4159_ = l_Lean_Elab_Do_elabDoArrow___lam__0(v_letOrReassign_4137_, v_otherwise_x3f_4138_, v___x_39001__boxed_4157_, v___x_4140_, v___x_4141_, v___x_4142_, v___x_4143_, v___x_4144_, v_dec_4145_, v___x_39007__boxed_4158_, v___y_4147_, v___x_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___x_4148_);
lean_dec(v_letOrReassign_4137_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1(lean_object* v_letOrReassign_4160_, lean_object* v_otherwise_x3f_4161_, uint8_t v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v_dec_4168_, uint8_t v___x_4169_, lean_object* v___y_4170_, lean_object* v___x_4171_, uint8_t v___x_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4204_; 
switch(lean_obj_tag(v_letOrReassign_4160_))
{
case 0:
{
if (lean_obj_tag(v_otherwise_x3f_4161_) == 1)
{
lean_object* v_mutTk_x3f_4215_; lean_object* v_val_4216_; lean_object* v_ref_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4247_; 
v_mutTk_x3f_4215_ = lean_ctor_get(v_letOrReassign_4160_, 0);
v_val_4216_ = lean_ctor_get(v_otherwise_x3f_4161_, 0);
lean_inc(v_val_4216_);
lean_dec_ref_known(v_otherwise_x3f_4161_, 1);
v_ref_4217_ = lean_ctor_get(v___y_4178_, 5);
v___x_4218_ = l_Lean_SourceInfo_fromRef(v_ref_4217_, v___x_4162_);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__3));
lean_inc_ref(v___x_4165_);
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
v___x_4220_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4219_);
v___x_4221_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4218_);
v___x_4222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4218_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4224_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4215_) == 1)
{
lean_object* v_val_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_val_4262_ = lean_ctor_get(v_mutTk_x3f_4215_, 0);
v___x_4263_ = l_Lean_SourceInfo_fromRef(v_val_4262_, v___x_4169_);
v___x_4264_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = l_Array_mkArray1___redArg(v___x_4265_);
v___y_4247_ = v___x_4266_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_mk_empty_array_with_capacity(v___x_4171_);
v___y_4247_ = v___x_4267_;
goto v___jp_4246_;
}
v___jp_4225_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4231_ = l_Array_append___redArg(v___x_4224_, v___y_4230_);
lean_dec_ref(v___y_4230_);
lean_inc(v___x_4218_);
v___x_4232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4218_);
lean_ctor_set(v___x_4232_, 1, v___x_4223_);
lean_ctor_set(v___x_4232_, 2, v___x_4231_);
v___x_4233_ = lean_unsigned_to_nat(9u);
v___x_4234_ = lean_mk_empty_array_with_capacity(v___x_4233_);
v___x_4235_ = lean_array_push(v___x_4234_, v___x_4222_);
v___x_4236_ = lean_array_push(v___x_4235_, v___y_4227_);
v___x_4237_ = lean_array_push(v___x_4236_, v___y_4229_);
v___x_4238_ = lean_array_push(v___x_4237_, v___x_4166_);
v___x_4239_ = lean_array_push(v___x_4238_, v___y_4228_);
v___x_4240_ = lean_array_push(v___x_4239_, v___x_4167_);
v___x_4241_ = lean_array_push(v___x_4240_, v___y_4226_);
v___x_4242_ = lean_array_push(v___x_4241_, v_val_4216_);
v___x_4243_ = lean_array_push(v___x_4242_, v___x_4232_);
v___x_4244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4218_);
lean_ctor_set(v___x_4244_, 1, v___x_4220_);
lean_ctor_set(v___x_4244_, 2, v___x_4243_);
v___x_4245_ = l_Lean_Elab_Do_elabDoElem(v___x_4244_, v_dec_4168_, v___x_4169_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4245_;
}
v___jp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4248_ = l_Array_append___redArg(v___x_4224_, v___y_4247_);
lean_dec_ref(v___y_4247_);
lean_inc_n(v___x_4218_, 5);
v___x_4249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4218_);
lean_ctor_set(v___x_4249_, 1, v___x_4223_);
lean_ctor_set(v___x_4249_, 2, v___x_4248_);
v___x_4250_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4251_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4250_);
v___x_4252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4218_);
lean_ctor_set(v___x_4252_, 1, v___x_4223_);
lean_ctor_set(v___x_4252_, 2, v___x_4224_);
v___x_4253_ = l_Lean_Syntax_node1(v___x_4218_, v___x_4251_, v___x_4252_);
v___x_4254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4218_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_4257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4218_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
if (lean_obj_tag(v___y_4170_) == 0)
{
lean_object* v___x_4258_; 
v___x_4258_ = lean_mk_empty_array_with_capacity(v___x_4171_);
v___y_4226_ = v___x_4257_;
v___y_4227_ = v___x_4249_;
v___y_4228_ = v___x_4255_;
v___y_4229_ = v___x_4253_;
v___y_4230_ = v___x_4258_;
goto v___jp_4225_;
}
else
{
lean_object* v_val_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_val_4259_ = lean_ctor_get(v___y_4170_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v___y_4170_, 1);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4171_);
v___x_4261_ = lean_array_push(v___x_4260_, v_val_4259_);
v___y_4226_ = v___x_4257_;
v___y_4227_ = v___x_4249_;
v___y_4228_ = v___x_4255_;
v___y_4229_ = v___x_4253_;
v___y_4230_ = v___x_4261_;
goto v___jp_4225_;
}
}
}
else
{
lean_object* v_mutTk_x3f_4268_; lean_object* v_ref_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___y_4278_; 
lean_dec(v___y_4170_);
lean_dec(v_otherwise_x3f_4161_);
v_mutTk_x3f_4268_ = lean_ctor_get(v_letOrReassign_4160_, 0);
v_ref_4269_ = lean_ctor_get(v___y_4178_, 5);
v___x_4270_ = l_Lean_SourceInfo_fromRef(v_ref_4269_, v___x_4162_);
v___x_4271_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__6));
lean_inc_ref(v___x_4165_);
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
v___x_4272_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4271_);
v___x_4273_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_4270_);
v___x_4274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4270_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4276_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_4268_) == 1)
{
lean_object* v_val_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_val_4295_ = lean_ctor_get(v_mutTk_x3f_4268_, 0);
v___x_4296_ = l_Lean_SourceInfo_fromRef(v_val_4295_, v___x_4169_);
v___x_4297_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_4298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Array_mkArray1___redArg(v___x_4298_);
v___y_4278_ = v___x_4299_;
goto v___jp_4277_;
}
else
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_mk_empty_array_with_capacity(v___x_4171_);
v___y_4278_ = v___x_4300_;
goto v___jp_4277_;
}
v___jp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4279_ = l_Array_append___redArg(v___x_4276_, v___y_4278_);
lean_dec_ref(v___y_4278_);
lean_inc_n(v___x_4270_, 6);
v___x_4280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4270_);
lean_ctor_set(v___x_4280_, 1, v___x_4275_);
lean_ctor_set(v___x_4280_, 2, v___x_4279_);
v___x_4281_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
lean_inc_ref_n(v___x_4165_, 2);
lean_inc_ref_n(v___x_4164_, 2);
lean_inc_ref_n(v___x_4163_, 2);
v___x_4282_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4281_);
v___x_4283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4270_);
lean_ctor_set(v___x_4283_, 1, v___x_4275_);
lean_ctor_set(v___x_4283_, 2, v___x_4276_);
lean_inc_ref_n(v___x_4283_, 2);
v___x_4284_ = l_Lean_Syntax_node1(v___x_4270_, v___x_4282_, v___x_4283_);
v___x_4285_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4286_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4285_);
v___x_4287_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4288_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4287_);
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4270_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Lean_Syntax_node5(v___x_4270_, v___x_4288_, v___x_4166_, v___x_4283_, v___x_4283_, v___x_4290_, v___x_4167_);
v___x_4292_ = l_Lean_Syntax_node1(v___x_4270_, v___x_4286_, v___x_4291_);
v___x_4293_ = l_Lean_Syntax_node4(v___x_4270_, v___x_4272_, v___x_4274_, v___x_4280_, v___x_4284_, v___x_4292_);
v___x_4294_ = l_Lean_Elab_Do_elabDoElem(v___x_4293_, v_dec_4168_, v___x_4169_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4294_;
}
}
}
case 1:
{
lean_dec(v___y_4170_);
if (lean_obj_tag(v_otherwise_x3f_4161_) == 1)
{
lean_object* v___x_4301_; 
lean_dec_ref_known(v_otherwise_x3f_4161_, 1);
lean_dec_ref(v_dec_4168_);
lean_dec(v___x_4167_);
lean_dec(v___x_4166_);
lean_dec_ref(v___x_4165_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v___x_4163_);
v___x_4301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4301_;
}
else
{
lean_object* v_ref_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
lean_dec(v_otherwise_x3f_4161_);
v_ref_4302_ = lean_ctor_get(v___y_4178_, 5);
v___x_4303_ = l_Lean_SourceInfo_fromRef(v_ref_4302_, v___x_4162_);
v___x_4304_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__7));
lean_inc_ref_n(v___x_4165_, 3);
lean_inc_ref_n(v___x_4164_, 3);
lean_inc_ref_n(v___x_4163_, 3);
v___x_4305_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4304_);
v___x_4306_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
lean_inc_n(v___x_4303_, 6);
v___x_4307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4303_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__4));
v___x_4309_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4308_);
v___x_4310_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4311_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4303_);
lean_ctor_set(v___x_4312_, 1, v___x_4310_);
lean_ctor_set(v___x_4312_, 2, v___x_4311_);
lean_inc_ref_n(v___x_4312_, 2);
v___x_4313_ = l_Lean_Syntax_node1(v___x_4303_, v___x_4309_, v___x_4312_);
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
v___x_4315_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4314_);
v___x_4316_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4317_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4316_);
v___x_4318_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4303_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l_Lean_Syntax_node5(v___x_4303_, v___x_4317_, v___x_4166_, v___x_4312_, v___x_4312_, v___x_4319_, v___x_4167_);
v___x_4321_ = l_Lean_Syntax_node1(v___x_4303_, v___x_4315_, v___x_4320_);
v___x_4322_ = l_Lean_Syntax_node3(v___x_4303_, v___x_4305_, v___x_4307_, v___x_4313_, v___x_4321_);
v___x_4323_ = l_Lean_Elab_Do_elabDoElem(v___x_4322_, v_dec_4168_, v___x_4169_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4323_;
}
}
default: 
{
lean_dec(v_otherwise_x3f_4161_);
if (lean_obj_tag(v___y_4170_) == 0)
{
v___y_4204_ = v___x_4172_;
goto v___jp_4203_;
}
else
{
lean_dec_ref_known(v___y_4170_, 1);
v___y_4204_ = v___x_4162_;
goto v___jp_4203_;
}
}
}
v___jp_4181_:
{
lean_object* v_ref_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_ref_4189_ = lean_ctor_get(v___y_4187_, 5);
v___x_4190_ = l_Lean_SourceInfo_fromRef(v_ref_4189_, v___x_4162_);
v___x_4191_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__0));
lean_inc_ref(v___x_4165_);
lean_inc_ref(v___x_4164_);
lean_inc_ref(v___x_4163_);
v___x_4192_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4191_);
v___x_4193_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_4194_ = l_Lean_Name_mkStr4(v___x_4163_, v___x_4164_, v___x_4165_, v___x_4193_);
v___x_4195_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4196_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_4190_, 3);
v___x_4197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4190_);
lean_ctor_set(v___x_4197_, 1, v___x_4195_);
lean_ctor_set(v___x_4197_, 2, v___x_4196_);
v___x_4198_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4190_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
lean_inc_ref(v___x_4197_);
v___x_4200_ = l_Lean_Syntax_node5(v___x_4190_, v___x_4194_, v___x_4166_, v___x_4197_, v___x_4197_, v___x_4199_, v___x_4167_);
v___x_4201_ = l_Lean_Syntax_node1(v___x_4190_, v___x_4192_, v___x_4200_);
v___x_4202_ = l_Lean_Elab_Do_elabDoElem(v___x_4201_, v_dec_4168_, v___x_4169_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
return v___x_4202_;
}
v___jp_4203_:
{
if (v___y_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_dec_4168_);
lean_dec(v___x_4167_);
lean_dec(v___x_4166_);
lean_dec_ref(v___x_4165_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v___x_4163_);
v___x_4205_ = lean_obj_once(&l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2, &l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2_once, _init_l_Lean_Elab_Do_elabDoArrow___lam__0___closed__2);
v___x_4206_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo_spec__0___redArg(v___x_4205_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
else
{
v___y_4182_ = v___y_4173_;
v___y_4183_ = v___y_4174_;
v___y_4184_ = v___y_4175_;
v___y_4185_ = v___y_4176_;
v___y_4186_ = v___y_4177_;
v___y_4187_ = v___y_4178_;
v___y_4188_ = v___y_4179_;
goto v___jp_4181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___lam__1___boxed(lean_object** _args){
lean_object* v_letOrReassign_4324_ = _args[0];
lean_object* v_otherwise_x3f_4325_ = _args[1];
lean_object* v___x_4326_ = _args[2];
lean_object* v___x_4327_ = _args[3];
lean_object* v___x_4328_ = _args[4];
lean_object* v___x_4329_ = _args[5];
lean_object* v___x_4330_ = _args[6];
lean_object* v___x_4331_ = _args[7];
lean_object* v_dec_4332_ = _args[8];
lean_object* v___x_4333_ = _args[9];
lean_object* v___y_4334_ = _args[10];
lean_object* v___x_4335_ = _args[11];
lean_object* v___x_4336_ = _args[12];
lean_object* v___y_4337_ = _args[13];
lean_object* v___y_4338_ = _args[14];
lean_object* v___y_4339_ = _args[15];
lean_object* v___y_4340_ = _args[16];
lean_object* v___y_4341_ = _args[17];
lean_object* v___y_4342_ = _args[18];
lean_object* v___y_4343_ = _args[19];
lean_object* v___y_4344_ = _args[20];
_start:
{
uint8_t v___x_39383__boxed_4345_; uint8_t v___x_39389__boxed_4346_; uint8_t v___x_39392__boxed_4347_; lean_object* v_res_4348_; 
v___x_39383__boxed_4345_ = lean_unbox(v___x_4326_);
v___x_39389__boxed_4346_ = lean_unbox(v___x_4333_);
v___x_39392__boxed_4347_ = lean_unbox(v___x_4336_);
v_res_4348_ = l_Lean_Elab_Do_elabDoArrow___lam__1(v_letOrReassign_4324_, v_otherwise_x3f_4325_, v___x_39383__boxed_4345_, v___x_4327_, v___x_4328_, v___x_4329_, v___x_4330_, v___x_4331_, v_dec_4332_, v___x_39389__boxed_4346_, v___y_4334_, v___x_4335_, v___x_39392__boxed_4347_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___x_4335_);
lean_dec(v_letOrReassign_4324_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow(lean_object* v_letOrReassign_4369_, lean_object* v_stx_4370_, lean_object* v_tk_4371_, lean_object* v_dec_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4382_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v_stx_4370_);
v___x_4385_ = l_Lean_Syntax_isOfKind(v_stx_4370_, v___x_4384_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v_stx_4370_);
v___x_4387_ = l_Lean_Syntax_isOfKind(v_stx_4370_, v___x_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; 
v___x_4389_ = lean_unsigned_to_nat(0u);
v___x_4390_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4389_);
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
lean_inc(v___x_4390_);
v___x_4392_ = l_Lean_Syntax_isOfKind(v___x_4390_, v___x_4391_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4478_; lean_object* v_patType_x3f_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4478_ = lean_unsigned_to_nat(1u);
v___x_4509_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4478_);
v___x_4510_ = l_Lean_Syntax_isNone(v___x_4509_);
if (v___x_4510_ == 0)
{
uint8_t v___x_4511_; 
lean_inc(v___x_4509_);
v___x_4511_ = l_Lean_Syntax_matchesNull(v___x_4509_, v___x_4478_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
lean_dec(v___x_4509_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4513_ = l_Lean_Syntax_getArg(v___x_4509_, v___x_4389_);
lean_dec(v___x_4509_);
v___x_4514_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4513_);
v___x_4515_ = l_Lean_Syntax_isOfKind(v___x_4513_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
lean_dec(v___x_4513_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4516_;
}
else
{
lean_object* v_patType_x3f_4517_; lean_object* v___x_4518_; 
v_patType_x3f_4517_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4478_);
lean_dec(v___x_4513_);
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_patType_x3f_4517_);
v_patType_x3f_4480_ = v___x_4518_;
v___y_4481_ = v_a_4373_;
v___y_4482_ = v_a_4374_;
v___y_4483_ = v_a_4375_;
v___y_4484_ = v_a_4376_;
v___y_4485_ = v_a_4377_;
v___y_4486_ = v_a_4378_;
v___y_4487_ = v_a_4379_;
goto v___jp_4479_;
}
}
}
else
{
lean_object* v___x_4519_; 
lean_dec(v___x_4509_);
v___x_4519_ = lean_box(0);
v_patType_x3f_4480_ = v___x_4519_;
v___y_4481_ = v_a_4373_;
v___y_4482_ = v_a_4374_;
v___y_4483_ = v_a_4375_;
v___y_4484_ = v_a_4376_;
v___y_4485_ = v_a_4377_;
v___y_4486_ = v_a_4378_;
v___y_4487_ = v_a_4379_;
goto v___jp_4479_;
}
v___jp_4479_:
{
lean_object* v___x_4488_; lean_object* v_rhs_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4488_ = lean_unsigned_to_nat(3u);
v_rhs_4489_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4488_);
v___x_4490_ = lean_unsigned_to_nat(4u);
v___x_4491_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4490_);
lean_dec(v_stx_4370_);
v___x_4492_ = l_Lean_Syntax_isNone(v___x_4491_);
if (v___x_4492_ == 0)
{
uint8_t v___x_4493_; 
lean_inc(v___x_4491_);
v___x_4493_ = l_Lean_Syntax_matchesNull(v___x_4491_, v___x_4488_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
lean_dec(v___x_4491_);
lean_dec(v_rhs_4489_);
lean_dec(v_patType_x3f_4480_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_letOrReassign_4369_);
v___x_4494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4494_;
}
else
{
lean_object* v___x_4495_; lean_object* v_otherwise_x3f_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4495_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4496_ = l_Lean_Syntax_getArg(v___x_4491_, v___x_4478_);
v___x_4497_ = l_Lean_Syntax_getArg(v___x_4491_, v___x_4495_);
lean_dec(v___x_4491_);
v___x_4498_ = l_Lean_Syntax_getOptional_x3f(v___x_4497_);
lean_dec(v___x_4497_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v___x_4499_; 
v___x_4499_ = lean_box(0);
v___y_4423_ = v_rhs_4489_;
v___y_4424_ = v_patType_x3f_4480_;
v___y_4425_ = v___y_4481_;
v___y_4426_ = v___y_4484_;
v___y_4427_ = v___y_4482_;
v___y_4428_ = v___y_4483_;
v___y_4429_ = v___y_4485_;
v___y_4430_ = v___y_4486_;
v___y_4431_ = v___y_4487_;
v___y_4432_ = v_otherwise_x3f_4496_;
v___y_4433_ = v___x_4499_;
goto v___jp_4422_;
}
else
{
lean_object* v_val_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_val_4500_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4498_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_val_4500_);
lean_dec(v___x_4498_);
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
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_val_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
v___y_4423_ = v_rhs_4489_;
v___y_4424_ = v_patType_x3f_4480_;
v___y_4425_ = v___y_4481_;
v___y_4426_ = v___y_4484_;
v___y_4427_ = v___y_4482_;
v___y_4428_ = v___y_4483_;
v___y_4429_ = v___y_4485_;
v___y_4430_ = v___y_4486_;
v___y_4431_ = v___y_4487_;
v___y_4432_ = v_otherwise_x3f_4496_;
v___y_4433_ = v___x_4505_;
goto v___jp_4422_;
}
}
}
}
}
else
{
lean_object* v___x_4508_; 
lean_dec(v___x_4491_);
v___x_4508_ = lean_box(0);
v___y_4394_ = v___y_4485_;
v___y_4395_ = v___y_4487_;
v___y_4396_ = v_rhs_4489_;
v___y_4397_ = v___y_4481_;
v___y_4398_ = v___x_4508_;
v___y_4399_ = v___y_4483_;
v___y_4400_ = v_patType_x3f_4480_;
v___y_4401_ = v___y_4482_;
v___y_4402_ = v___y_4486_;
v___y_4403_ = v___y_4484_;
v___y_4404_ = v___x_4508_;
goto v___jp_4393_;
}
}
}
else
{
lean_object* v_pattern_4520_; lean_object* v___x_4521_; lean_object* v_patType_x3f_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___x_4578_; uint8_t v___x_4579_; 
v_pattern_4520_ = l_Lean_Syntax_getArg(v___x_4390_, v___x_4389_);
v___x_4521_ = lean_unsigned_to_nat(1u);
v___x_4578_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4521_);
v___x_4579_ = l_Lean_Syntax_isNone(v___x_4578_);
if (v___x_4579_ == 0)
{
uint8_t v___x_4580_; 
lean_inc(v___x_4578_);
v___x_4580_ = l_Lean_Syntax_matchesNull(v___x_4578_, v___x_4521_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
lean_dec(v___x_4578_);
lean_dec(v_pattern_4520_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4581_;
}
else
{
lean_object* v___x_4582_; lean_object* v___x_4583_; uint8_t v___x_4584_; 
v___x_4582_ = l_Lean_Syntax_getArg(v___x_4578_, v___x_4389_);
lean_dec(v___x_4578_);
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4582_);
v___x_4584_ = l_Lean_Syntax_isOfKind(v___x_4582_, v___x_4583_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; 
lean_dec(v___x_4582_);
lean_dec(v_pattern_4520_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4585_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4585_;
}
else
{
lean_object* v_patType_x3f_4586_; lean_object* v___x_4587_; 
v_patType_x3f_4586_ = l_Lean_Syntax_getArg(v___x_4582_, v___x_4521_);
lean_dec(v___x_4582_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_patType_x3f_4586_);
v_patType_x3f_4523_ = v___x_4587_;
v___y_4524_ = v_a_4373_;
v___y_4525_ = v_a_4374_;
v___y_4526_ = v_a_4375_;
v___y_4527_ = v_a_4376_;
v___y_4528_ = v_a_4377_;
v___y_4529_ = v_a_4378_;
v___y_4530_ = v_a_4379_;
goto v___jp_4522_;
}
}
}
else
{
lean_object* v___x_4588_; 
lean_dec(v___x_4578_);
v___x_4588_ = lean_box(0);
v_patType_x3f_4523_ = v___x_4588_;
v___y_4524_ = v_a_4373_;
v___y_4525_ = v_a_4374_;
v___y_4526_ = v_a_4375_;
v___y_4527_ = v_a_4376_;
v___y_4528_ = v_a_4377_;
v___y_4529_ = v_a_4378_;
v___y_4530_ = v_a_4379_;
goto v___jp_4522_;
}
v___jp_4522_:
{
lean_object* v___x_4531_; lean_object* v_rhs_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4531_ = lean_unsigned_to_nat(3u);
v_rhs_4532_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4531_);
v___x_4533_ = lean_unsigned_to_nat(4u);
v___x_4534_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4533_);
lean_dec(v_stx_4370_);
lean_inc(v___x_4534_);
v___x_4535_ = l_Lean_Syntax_matchesNull(v___x_4534_, v___x_4389_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
lean_dec(v_pattern_4520_);
v___x_4536_ = l_Lean_Syntax_isNone(v___x_4534_);
if (v___x_4536_ == 0)
{
uint8_t v___x_4537_; 
lean_inc(v___x_4534_);
v___x_4537_ = l_Lean_Syntax_matchesNull(v___x_4534_, v___x_4531_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; 
lean_dec(v___x_4534_);
lean_dec(v_rhs_4532_);
lean_dec(v_patType_x3f_4523_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_letOrReassign_4369_);
v___x_4538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; lean_object* v_otherwise_x3f_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4539_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_4540_ = l_Lean_Syntax_getArg(v___x_4534_, v___x_4521_);
v___x_4541_ = l_Lean_Syntax_getArg(v___x_4534_, v___x_4539_);
lean_dec(v___x_4534_);
v___x_4542_ = l_Lean_Syntax_getOptional_x3f(v___x_4541_);
lean_dec(v___x_4541_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_box(0);
v___y_4466_ = v___y_4526_;
v___y_4467_ = v___y_4527_;
v___y_4468_ = v_otherwise_x3f_4540_;
v___y_4469_ = v___y_4528_;
v___y_4470_ = v_patType_x3f_4523_;
v___y_4471_ = v___y_4530_;
v___y_4472_ = v_rhs_4532_;
v___y_4473_ = v___y_4524_;
v___y_4474_ = v___y_4529_;
v___y_4475_ = v___y_4525_;
v___y_4476_ = v___x_4543_;
goto v___jp_4465_;
}
else
{
lean_object* v_val_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_val_4544_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4542_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_val_4544_);
lean_dec(v___x_4542_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_val_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
v___y_4466_ = v___y_4526_;
v___y_4467_ = v___y_4527_;
v___y_4468_ = v_otherwise_x3f_4540_;
v___y_4469_ = v___y_4528_;
v___y_4470_ = v_patType_x3f_4523_;
v___y_4471_ = v___y_4530_;
v___y_4472_ = v_rhs_4532_;
v___y_4473_ = v___y_4524_;
v___y_4474_ = v___y_4529_;
v___y_4475_ = v___y_4525_;
v___y_4476_ = v___x_4549_;
goto v___jp_4465_;
}
}
}
}
}
else
{
lean_object* v___x_4552_; 
lean_dec(v___x_4534_);
v___x_4552_ = lean_box(0);
v___y_4436_ = v_rhs_4532_;
v___y_4437_ = v___y_4528_;
v___y_4438_ = v___y_4525_;
v___y_4439_ = v___y_4527_;
v___y_4440_ = v___y_4526_;
v___y_4441_ = v___y_4530_;
v___y_4442_ = v___y_4529_;
v___y_4443_ = v___y_4524_;
v___y_4444_ = v_patType_x3f_4523_;
v___y_4445_ = v___x_4552_;
v___y_4446_ = v___x_4552_;
goto v___jp_4435_;
}
}
else
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
lean_dec(v___x_4534_);
lean_dec(v___x_4390_);
lean_dec(v_letOrReassign_4369_);
v___x_4553_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4554_ = l_Lean_Core_mkFreshUserName(v___x_4553_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v___x_4556_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4372_, v_tk_4371_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; uint8_t v_kind_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
v_kind_4558_ = lean_ctor_get_uint8(v_a_4557_, sizeof(void*)*3);
v___x_4559_ = l_Lean_mkIdentFrom(v_pattern_4520_, v_a_4555_, v___x_4385_);
lean_dec(v_pattern_4520_);
v___x_4560_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4560_, 0, v_a_4557_);
v___x_4561_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4559_, v_patType_x3f_4523_, v_rhs_4532_, v___x_4560_, v_kind_4558_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4561_;
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_a_4555_);
lean_dec(v_rhs_4532_);
lean_dec(v_patType_x3f_4523_);
lean_dec(v_pattern_4520_);
v_a_4562_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4556_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4556_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v_rhs_4532_);
lean_dec(v_patType_x3f_4523_);
lean_dec(v_pattern_4520_);
lean_dec_ref(v_dec_4372_);
v_a_4570_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4554_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4554_);
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
}
}
}
v___jp_4393_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4406_ = l_Lean_Core_mkFreshUserName(v___x_4405_, v___y_4402_, v___y_4395_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___y_4411_; uint8_t v___x_4412_; lean_object* v___x_4413_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = l_Lean_mkIdentFrom(v___x_4390_, v_a_4407_, v___x_4392_);
v___x_4409_ = lean_box(v___x_4392_);
v___x_4410_ = lean_box(v___x_4387_);
lean_inc(v___x_4408_);
v___y_4411_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__0___boxed), 20, 12);
lean_closure_set(v___y_4411_, 0, v_letOrReassign_4369_);
lean_closure_set(v___y_4411_, 1, v___y_4398_);
lean_closure_set(v___y_4411_, 2, v___x_4409_);
lean_closure_set(v___y_4411_, 3, v___x_4381_);
lean_closure_set(v___y_4411_, 4, v___x_4382_);
lean_closure_set(v___y_4411_, 5, v___x_4383_);
lean_closure_set(v___y_4411_, 6, v___x_4390_);
lean_closure_set(v___y_4411_, 7, v___x_4408_);
lean_closure_set(v___y_4411_, 8, v_dec_4372_);
lean_closure_set(v___y_4411_, 9, v___x_4410_);
lean_closure_set(v___y_4411_, 10, v___y_4404_);
lean_closure_set(v___y_4411_, 11, v___x_4389_);
v___x_4412_ = 0;
v___x_4413_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4408_, v___y_4400_, v___y_4396_, v___y_4411_, v___x_4412_, v___y_4397_, v___y_4401_, v___y_4399_, v___y_4403_, v___y_4394_, v___y_4402_, v___y_4395_);
return v___x_4413_;
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v___y_4404_);
lean_dec(v___y_4400_);
lean_dec(v___y_4398_);
lean_dec(v___y_4396_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_letOrReassign_4369_);
v_a_4414_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4406_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4406_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
v___jp_4422_:
{
lean_object* v___x_4434_; 
v___x_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___y_4432_);
v___y_4394_ = v___y_4429_;
v___y_4395_ = v___y_4431_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4425_;
v___y_4398_ = v___x_4434_;
v___y_4399_ = v___y_4428_;
v___y_4400_ = v___y_4424_;
v___y_4401_ = v___y_4427_;
v___y_4402_ = v___y_4430_;
v___y_4403_ = v___y_4426_;
v___y_4404_ = v___y_4433_;
goto v___jp_4393_;
}
v___jp_4435_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4447_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__6));
v___x_4448_ = l_Lean_Core_mkFreshUserName(v___x_4447_, v___y_4442_, v___y_4441_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___y_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref_known(v___x_4448_, 1);
v___x_4450_ = l_Lean_mkIdentFrom(v___x_4390_, v_a_4449_, v___x_4385_);
v___x_4451_ = lean_box(v___x_4385_);
v___x_4452_ = lean_box(v___x_4387_);
v___x_4453_ = lean_box(v___x_4392_);
lean_inc(v___x_4450_);
v___y_4454_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_4454_, 0, v_letOrReassign_4369_);
lean_closure_set(v___y_4454_, 1, v___y_4445_);
lean_closure_set(v___y_4454_, 2, v___x_4451_);
lean_closure_set(v___y_4454_, 3, v___x_4381_);
lean_closure_set(v___y_4454_, 4, v___x_4382_);
lean_closure_set(v___y_4454_, 5, v___x_4383_);
lean_closure_set(v___y_4454_, 6, v___x_4390_);
lean_closure_set(v___y_4454_, 7, v___x_4450_);
lean_closure_set(v___y_4454_, 8, v_dec_4372_);
lean_closure_set(v___y_4454_, 9, v___x_4452_);
lean_closure_set(v___y_4454_, 10, v___y_4446_);
lean_closure_set(v___y_4454_, 11, v___x_4389_);
lean_closure_set(v___y_4454_, 12, v___x_4453_);
v___x_4455_ = 0;
v___x_4456_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_4450_, v___y_4444_, v___y_4436_, v___y_4454_, v___x_4455_, v___y_4443_, v___y_4438_, v___y_4440_, v___y_4439_, v___y_4437_, v___y_4442_, v___y_4441_);
return v___x_4456_;
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec(v___y_4436_);
lean_dec(v___x_4390_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_letOrReassign_4369_);
v_a_4457_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4448_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4448_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
v___jp_4465_:
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___y_4468_);
v___y_4436_ = v___y_4472_;
v___y_4437_ = v___y_4469_;
v___y_4438_ = v___y_4475_;
v___y_4439_ = v___y_4467_;
v___y_4440_ = v___y_4466_;
v___y_4441_ = v___y_4471_;
v___y_4442_ = v___y_4474_;
v___y_4443_ = v___y_4473_;
v___y_4444_ = v___y_4470_;
v___y_4445_ = v___x_4477_;
v___y_4446_ = v___y_4476_;
goto v___jp_4435_;
}
}
}
else
{
lean_object* v___x_4589_; lean_object* v_x_4590_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v_xType_x3f_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v_xType_x3f_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___x_4663_; uint8_t v___x_4664_; 
v___x_4589_ = lean_unsigned_to_nat(0u);
v_x_4590_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4589_);
v___x_4663_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_4590_);
v___x_4664_ = l_Lean_Syntax_isOfKind(v_x_4590_, v___x_4663_);
if (v___x_4664_ == 0)
{
lean_object* v___x_4665_; 
lean_dec(v_x_4590_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4665_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; 
v___x_4666_ = lean_unsigned_to_nat(1u);
v___x_4667_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4666_);
v___x_4668_ = l_Lean_Syntax_isNone(v___x_4667_);
if (v___x_4668_ == 0)
{
uint8_t v___x_4669_; 
lean_inc(v___x_4667_);
v___x_4669_ = l_Lean_Syntax_matchesNull(v___x_4667_, v___x_4666_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
lean_dec(v___x_4667_);
lean_dec(v_x_4590_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4670_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4670_;
}
else
{
lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4671_ = l_Lean_Syntax_getArg(v___x_4667_, v___x_4589_);
lean_dec(v___x_4667_);
v___x_4672_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4671_);
v___x_4673_ = l_Lean_Syntax_isOfKind(v___x_4671_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
lean_dec(v___x_4671_);
lean_dec(v_x_4590_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v___x_4674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4674_;
}
else
{
lean_object* v_xType_x3f_4675_; lean_object* v___x_4676_; 
v_xType_x3f_4675_ = l_Lean_Syntax_getArg(v___x_4671_, v___x_4666_);
lean_dec(v___x_4671_);
v___x_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_xType_x3f_4675_);
v_xType_x3f_4608_ = v___x_4676_;
v___y_4609_ = v_a_4373_;
v___y_4610_ = v_a_4374_;
v___y_4611_ = v_a_4375_;
v___y_4612_ = v_a_4376_;
v___y_4613_ = v_a_4377_;
v___y_4614_ = v_a_4378_;
v___y_4615_ = v_a_4379_;
goto v___jp_4607_;
}
}
}
else
{
lean_object* v___x_4677_; 
lean_dec(v___x_4667_);
v___x_4677_ = lean_box(0);
v_xType_x3f_4608_ = v___x_4677_;
v___y_4609_ = v_a_4373_;
v___y_4610_ = v_a_4374_;
v___y_4611_ = v_a_4375_;
v___y_4612_ = v_a_4376_;
v___y_4613_ = v_a_4377_;
v___y_4614_ = v_a_4378_;
v___y_4615_ = v_a_4379_;
goto v___jp_4607_;
}
}
v___jp_4591_:
{
uint8_t v_kind_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v_kind_4602_ = lean_ctor_get_uint8(v___y_4593_, sizeof(void*)*3);
v___x_4603_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_4369_);
lean_dec(v_letOrReassign_4369_);
v___x_4604_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4604_, 0, v___y_4593_);
lean_inc(v_x_4590_);
v___x_4605_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 12, 4);
lean_closure_set(v___x_4605_, 0, lean_box(0));
lean_closure_set(v___x_4605_, 1, v___x_4603_);
lean_closure_set(v___x_4605_, 2, v_x_4590_);
lean_closure_set(v___x_4605_, 3, v___x_4604_);
v___x_4606_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_4590_, v_xType_x3f_4594_, v___y_4592_, v___x_4605_, v_kind_4602_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
return v___x_4606_;
}
v___jp_4607_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4616_ = lean_unsigned_to_nat(1u);
v___x_4617_ = lean_mk_empty_array_with_capacity(v___x_4616_);
lean_inc(v_x_4590_);
v___x_4618_ = lean_array_push(v___x_4617_, v_x_4590_);
v___x_4619_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_4369_, v___x_4618_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
lean_dec_ref(v___x_4618_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4620_; 
lean_dec_ref_known(v___x_4619_, 1);
v___x_4620_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4372_, v_tk_4371_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; lean_object* v_rhs_4623_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref_known(v___x_4620_, 1);
v___x_4622_ = lean_unsigned_to_nat(3u);
v_rhs_4623_ = l_Lean_Syntax_getArg(v_stx_4370_, v___x_4622_);
lean_dec(v_stx_4370_);
if (lean_obj_tag(v_letOrReassign_4369_) == 2)
{
if (lean_obj_tag(v_xType_x3f_4608_) == 0)
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = l_Lean_TSyntax_getId(v_x_4590_);
v___x_4625_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4624_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref_known(v___x_4625_, 1);
v___x_4627_ = l_Lean_LocalDecl_type(v_a_4626_);
lean_dec(v_a_4626_);
v___x_4628_ = l_Lean_Elab_Term_exprToSyntax(v___x_4627_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_a_4629_);
v___y_4592_ = v_rhs_4623_;
v___y_4593_ = v_a_4621_;
v_xType_x3f_4594_ = v___x_4630_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
v___y_4601_ = v___y_4615_;
goto v___jp_4591_;
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec(v_rhs_4623_);
lean_dec(v_a_4621_);
lean_dec(v_x_4590_);
v_a_4631_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4628_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4628_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec(v_rhs_4623_);
lean_dec(v_a_4621_);
lean_dec(v_x_4590_);
v_a_4639_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4625_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4625_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
else
{
v___y_4592_ = v_rhs_4623_;
v___y_4593_ = v_a_4621_;
v_xType_x3f_4594_ = v_xType_x3f_4608_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
v___y_4601_ = v___y_4615_;
goto v___jp_4591_;
}
}
else
{
v___y_4592_ = v_rhs_4623_;
v___y_4593_ = v_a_4621_;
v_xType_x3f_4594_ = v_xType_x3f_4608_;
v___y_4595_ = v___y_4609_;
v___y_4596_ = v___y_4610_;
v___y_4597_ = v___y_4611_;
v___y_4598_ = v___y_4612_;
v___y_4599_ = v___y_4613_;
v___y_4600_ = v___y_4614_;
v___y_4601_ = v___y_4615_;
goto v___jp_4591_;
}
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_xType_x3f_4608_);
lean_dec(v_x_4590_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v_a_4647_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4620_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4620_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec(v_xType_x3f_4608_);
lean_dec(v_x_4590_);
lean_dec_ref(v_dec_4372_);
lean_dec(v_stx_4370_);
lean_dec(v_letOrReassign_4369_);
v_a_4655_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4619_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4619_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoArrow___boxed(lean_object* v_letOrReassign_4678_, lean_object* v_stx_4679_, lean_object* v_tk_4680_, lean_object* v_dec_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_Elab_Do_elabDoArrow(v_letOrReassign_4678_, v_stx_4679_, v_tk_4680_, v_dec_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_tk_4680_);
return v_res_4690_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__0));
v___x_4693_ = l_Lean_stringToMessageData(v___x_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(lean_object* v_letConfigStx_4694_, lean_object* v_mutTk_x3f_4695_, lean_object* v_initConfig_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4695_) == 0)
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4694_, v_initConfig_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
return v___x_4704_;
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = l_Lean_Syntax_getArg(v_letConfigStx_4694_, v___x_4705_);
v___x_4707_ = l_Lean_Syntax_getArgs(v___x_4706_);
lean_dec(v___x_4706_);
v___x_4708_ = lean_array_get_size(v___x_4707_);
lean_dec_ref(v___x_4707_);
v___x_4709_ = lean_nat_dec_eq(v___x_4708_, v___x_4705_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
lean_dec_ref(v_initConfig_4696_);
v___x_4710_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___closed__1);
v___x_4711_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v_letConfigStx_4694_, v___x_4710_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_letConfigStx_4694_);
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
else
{
lean_object* v___x_4720_; 
v___x_4720_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4694_, v_initConfig_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
return v___x_4720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg___boxed(lean_object* v_letConfigStx_4721_, lean_object* v_mutTk_x3f_4722_, lean_object* v_initConfig_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4721_, v_mutTk_x3f_4722_, v_initConfig_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_mutTk_x3f_4722_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4732_, lean_object* v_mutTk_x3f_4733_, lean_object* v_initConfig_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_letConfigStx_4732_, v_mutTk_x3f_4733_, v_initConfig_4734_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4744_, lean_object* v_mutTk_x3f_4745_, lean_object* v_initConfig_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4744_, v_mutTk_x3f_4745_, v_initConfig_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec_ref(v_a_4747_);
lean_dec(v_mutTk_x3f_4745_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4769_, lean_object* v_dec_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4779_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc(v_stx_4769_);
v___x_4780_ = l_Lean_Syntax_isOfKind(v_stx_4769_, v___x_4779_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; 
lean_dec_ref(v_dec_4770_);
lean_dec(v_stx_4769_);
v___x_4781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4781_;
}
else
{
lean_object* v___x_4782_; lean_object* v_tk_4783_; lean_object* v_mutTk_x3f_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___x_4782_ = lean_unsigned_to_nat(0u);
v_tk_4783_ = l_Lean_Syntax_getArg(v_stx_4769_, v___x_4782_);
v___x_4816_ = lean_unsigned_to_nat(1u);
v___x_4817_ = l_Lean_Syntax_getArg(v_stx_4769_, v___x_4816_);
v___x_4818_ = l_Lean_Syntax_isNone(v___x_4817_);
if (v___x_4818_ == 0)
{
uint8_t v___x_4819_; 
lean_inc(v___x_4817_);
v___x_4819_ = l_Lean_Syntax_matchesNull(v___x_4817_, v___x_4816_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; 
lean_dec(v___x_4817_);
lean_dec(v_tk_4783_);
lean_dec_ref(v_dec_4770_);
lean_dec(v_stx_4769_);
v___x_4820_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4820_;
}
else
{
lean_object* v_mutTk_x3f_4821_; lean_object* v___x_4822_; 
v_mutTk_x3f_4821_ = l_Lean_Syntax_getArg(v___x_4817_, v___x_4782_);
lean_dec(v___x_4817_);
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_mutTk_x3f_4821_);
v_mutTk_x3f_4785_ = v___x_4822_;
v___y_4786_ = v_a_4771_;
v___y_4787_ = v_a_4772_;
v___y_4788_ = v_a_4773_;
v___y_4789_ = v_a_4774_;
v___y_4790_ = v_a_4775_;
v___y_4791_ = v_a_4776_;
v___y_4792_ = v_a_4777_;
goto v___jp_4784_;
}
}
else
{
lean_object* v___x_4823_; 
lean_dec(v___x_4817_);
v___x_4823_ = lean_box(0);
v_mutTk_x3f_4785_ = v___x_4823_;
v___y_4786_ = v_a_4771_;
v___y_4787_ = v_a_4772_;
v___y_4788_ = v_a_4773_;
v___y_4789_ = v_a_4774_;
v___y_4790_ = v_a_4775_;
v___y_4791_ = v_a_4776_;
v___y_4792_ = v_a_4777_;
goto v___jp_4784_;
}
v___jp_4784_:
{
lean_object* v___x_4793_; lean_object* v_config_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; 
v___x_4793_ = lean_unsigned_to_nat(2u);
v_config_4794_ = l_Lean_Syntax_getArg(v_stx_4769_, v___x_4793_);
v___x_4795_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_config_4794_);
v___x_4796_ = l_Lean_Syntax_isOfKind(v_config_4794_, v___x_4795_);
if (v___x_4796_ == 0)
{
lean_object* v___x_4797_; 
lean_dec(v_config_4794_);
lean_dec(v_mutTk_x3f_4785_);
lean_dec(v_tk_4783_);
lean_dec_ref(v_dec_4770_);
lean_dec(v_stx_4769_);
v___x_4797_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4797_;
}
else
{
lean_object* v___x_4798_; lean_object* v_decl_4799_; lean_object* v___x_4800_; uint8_t v___x_4801_; 
v___x_4798_ = lean_unsigned_to_nat(3u);
v_decl_4799_ = l_Lean_Syntax_getArg(v_stx_4769_, v___x_4798_);
lean_dec(v_stx_4769_);
v___x_4800_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4799_);
v___x_4801_ = l_Lean_Syntax_isOfKind(v_decl_4799_, v___x_4800_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; 
lean_dec(v_decl_4799_);
lean_dec(v_config_4794_);
lean_dec(v_mutTk_x3f_4785_);
lean_dec(v_tk_4783_);
lean_dec_ref(v_dec_4770_);
v___x_4802_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4802_;
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_4804_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_config_4794_, v_mutTk_x3f_4785_, v___x_4803_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v_mutTk_x3f_4785_);
v___x_4807_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4805_, v___x_4806_, v_decl_4799_, v_tk_4783_, v_dec_4770_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4807_;
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_decl_4799_);
lean_dec(v_mutTk_x3f_4785_);
lean_dec(v_tk_4783_);
lean_dec_ref(v_dec_4770_);
v_a_4808_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4804_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4804_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4824_, lean_object* v_dec_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_Elab_Do_elabDoLet(v_stx_4824_, v_dec_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec_ref(v_a_4826_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4842_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4843_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_4844_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4845_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4846_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4842_, v___x_4843_, v___x_4844_, v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4854_, lean_object* v_dec_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4864_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
lean_inc(v_stx_4854_);
v___x_4865_ = l_Lean_Syntax_isOfKind(v_stx_4854_, v___x_4864_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; 
lean_dec_ref(v_dec_4855_);
lean_dec(v_stx_4854_);
v___x_4866_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4866_;
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4867_ = lean_unsigned_to_nat(1u);
v___x_4868_ = l_Lean_Syntax_getArg(v_stx_4854_, v___x_4867_);
v___x_4869_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v___x_4868_);
v___x_4870_ = l_Lean_Syntax_isOfKind(v___x_4868_, v___x_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
lean_dec(v___x_4868_);
lean_dec_ref(v_dec_4855_);
lean_dec(v_stx_4854_);
v___x_4871_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4871_;
}
else
{
lean_object* v___x_4872_; lean_object* v_decl_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; 
v___x_4872_ = lean_unsigned_to_nat(2u);
v_decl_4873_ = l_Lean_Syntax_getArg(v_stx_4854_, v___x_4872_);
v___x_4874_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4873_);
v___x_4875_ = l_Lean_Syntax_isOfKind(v_decl_4873_, v___x_4874_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; 
lean_dec(v_decl_4873_);
lean_dec(v___x_4868_);
lean_dec_ref(v_dec_4855_);
lean_dec(v_stx_4854_);
v___x_4876_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_4876_;
}
else
{
uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4877_ = 0;
v___x_4878_ = lean_box(0);
v___x_4879_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*1, v___x_4875_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*1 + 1, v___x_4877_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*1 + 2, v___x_4877_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*1 + 3, v___x_4877_);
lean_ctor_set_uint8(v___x_4879_, sizeof(void*)*1 + 4, v___x_4877_);
v___x_4880_ = l_Lean_Elab_Term_mkLetConfig(v___x_4868_, v___x_4879_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; lean_object* v_tk_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref_known(v___x_4880_, 1);
v___x_4882_ = lean_unsigned_to_nat(0u);
v_tk_4883_ = l_Lean_Syntax_getArg(v_stx_4854_, v___x_4882_);
lean_dec(v_stx_4854_);
v___x_4884_ = lean_box(1);
v___x_4885_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4881_, v___x_4884_, v_decl_4873_, v_tk_4883_, v_dec_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
return v___x_4885_;
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
lean_dec(v_decl_4873_);
lean_dec_ref(v_dec_4855_);
lean_dec(v_stx_4854_);
v_a_4886_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4880_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4880_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4894_, lean_object* v_dec_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Elab_Do_elabDoHave(v_stx_4894_, v_dec_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
lean_dec_ref(v_a_4896_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4912_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4913_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__0));
v___x_4914_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4915_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4912_, v___x_4913_, v___x_4914_, v___x_4915_);
return v___x_4916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v___x_4924_, lean_object* v_decls_4925_, lean_object* v_a_4926_, uint8_t v___x_4927_, lean_object* v_body_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v_ref_4937_; uint8_t v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_ref_4937_ = lean_ctor_get(v___y_4934_, 5);
v___x_4938_ = 0;
v___x_4939_ = l_Lean_SourceInfo_fromRef(v_ref_4937_, v___x_4938_);
v___x_4940_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4941_ = l_Lean_Name_mkStr4(v___x_4921_, v___x_4922_, v___x_4923_, v___x_4940_);
v___x_4942_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4939_, 4);
v___x_4943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4939_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4939_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = l_Lean_Syntax_node2(v___x_4939_, v___x_4924_, v___x_4943_, v___x_4945_);
v___x_4947_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_4948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4939_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = l_Lean_Syntax_node4(v___x_4939_, v___x_4941_, v___x_4946_, v_decls_4925_, v___x_4948_, v_body_4928_);
v___x_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4950_, 0, v_a_4926_);
v___x_4951_ = l_Lean_Elab_Term_elabTerm(v___x_4949_, v___x_4950_, v___x_4927_, v___x_4927_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4952_, lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v___x_4955_, lean_object* v_decls_4956_, lean_object* v_a_4957_, lean_object* v___x_4958_, lean_object* v_body_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
uint8_t v___x_5027__boxed_4968_; lean_object* v_res_4969_; 
v___x_5027__boxed_4968_ = lean_unbox(v___x_4958_);
v_res_4969_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4952_, v___x_4953_, v___x_4954_, v___x_4955_, v_decls_4956_, v_a_4957_, v___x_5027__boxed_4968_, v_body_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec_ref(v___y_4960_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
if (lean_obj_tag(v_a_4970_) == 0)
{
lean_object* v___x_4972_; 
v___x_4972_ = l_List_reverse___redArg(v_a_4971_);
return v___x_4972_;
}
else
{
lean_object* v_head_4973_; lean_object* v_tail_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4983_; 
v_head_4973_ = lean_ctor_get(v_a_4970_, 0);
v_tail_4974_ = lean_ctor_get(v_a_4970_, 1);
v_isSharedCheck_4983_ = !lean_is_exclusive(v_a_4970_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4976_ = v_a_4970_;
v_isShared_4977_ = v_isSharedCheck_4983_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_tail_4974_);
lean_inc(v_head_4973_);
lean_dec(v_a_4970_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4983_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; lean_object* v___x_4980_; 
v___x_4978_ = l_Lean_MessageData_ofSyntax(v_head_4973_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v_a_4971_);
lean_ctor_set(v___x_4976_, 0, v___x_4978_);
v___x_4980_ = v___x_4976_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4978_);
lean_ctor_set(v_reuseFailAlloc_4982_, 1, v_a_4971_);
v___x_4980_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
v_a_4970_ = v_tail_4974_;
v_a_4971_ = v___x_4980_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_5001_ = l_Lean_stringToMessageData(v___x_5000_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_5002_, lean_object* v_dec_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
v___x_5012_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5013_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5014_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5015_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_5002_);
v___x_5016_ = l_Lean_Syntax_isOfKind(v_stx_5002_, v___x_5015_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; 
lean_dec_ref(v_dec_5003_);
lean_dec(v_stx_5002_);
v___x_5017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5017_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; uint8_t v___x_5021_; 
v___x_5018_ = lean_unsigned_to_nat(0u);
v___x_5019_ = l_Lean_Syntax_getArg(v_stx_5002_, v___x_5018_);
v___x_5020_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_5019_);
v___x_5021_ = l_Lean_Syntax_isOfKind(v___x_5019_, v___x_5020_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
lean_dec(v___x_5019_);
lean_dec_ref(v_dec_5003_);
lean_dec(v_stx_5002_);
v___x_5022_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5022_;
}
else
{
lean_object* v___x_5023_; lean_object* v_decls_5024_; lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5023_ = lean_unsigned_to_nat(1u);
v_decls_5024_ = l_Lean_Syntax_getArg(v_stx_5002_, v___x_5023_);
lean_dec(v_stx_5002_);
v___x_5025_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_5024_);
v___x_5026_ = l_Lean_Syntax_isOfKind(v_decls_5024_, v___x_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec(v_decls_5024_);
lean_dec(v___x_5019_);
lean_dec_ref(v_dec_5003_);
v___x_5027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5027_;
}
else
{
lean_object* v_tk_5028_; lean_object* v___x_5029_; 
v_tk_5028_ = l_Lean_Syntax_getArg(v___x_5019_, v___x_5018_);
lean_dec(v___x_5019_);
v___x_5029_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5003_, v_tk_5028_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_tk_5028_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v___x_5031_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___x_5029_, 1);
lean_inc(v_decls_5024_);
v___x_5031_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_5024_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v_doBlockResultType_5033_; lean_object* v___x_5034_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v_doBlockResultType_5033_ = lean_ctor_get(v_a_5004_, 3);
lean_inc_ref(v_doBlockResultType_5033_);
v___x_5034_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_5033_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
v___x_5036_ = lean_box(v___x_5026_);
v___f_5037_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_5037_, 0, v___x_5012_);
lean_closure_set(v___f_5037_, 1, v___x_5013_);
lean_closure_set(v___f_5037_, 2, v___x_5014_);
lean_closure_set(v___f_5037_, 3, v___x_5020_);
lean_closure_set(v___f_5037_, 4, v_decls_5024_);
lean_closure_set(v___f_5037_, 5, v_a_5035_);
lean_closure_set(v___f_5037_, 6, v___x_5036_);
v___x_5038_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_5039_ = lean_array_to_list(v_a_5032_);
v___x_5040_ = lean_box(0);
v___x_5041_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_5039_, v___x_5040_);
v___x_5042_ = l_Lean_MessageData_ofList(v___x_5041_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5038_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_5044_, 0, v_a_5030_);
v___x_5045_ = lean_box(0);
v___x_5046_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_5043_, v___x_5044_, v___f_5037_, v___x_5045_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
return v___x_5046_;
}
else
{
lean_dec(v_a_5032_);
lean_dec(v_a_5030_);
lean_dec(v_decls_5024_);
return v___x_5034_;
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec(v_a_5030_);
lean_dec(v_decls_5024_);
v_a_5047_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5031_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5031_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
else
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5062_; 
lean_dec(v_decls_5024_);
v_a_5055_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5057_ = v___x_5029_;
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v___x_5029_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5060_; 
if (v_isShared_5058_ == 0)
{
v___x_5060_ = v___x_5057_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5063_, lean_object* v_dec_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5063_, v_dec_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec_ref(v_a_5065_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5081_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5083_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5084_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5085_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5081_, v___x_5082_, v___x_5083_, v___x_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5101_, lean_object* v_dec_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; uint8_t v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___y_5128_; lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
lean_inc(v_stx_5101_);
v___x_5145_ = l_Lean_Syntax_isOfKind(v_stx_5101_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
lean_dec_ref(v_dec_5102_);
lean_dec(v_stx_5101_);
v___x_5146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5146_;
}
else
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; 
v___x_5147_ = lean_unsigned_to_nat(0u);
v___x_5148_ = l_Lean_Syntax_getArg(v_stx_5101_, v___x_5147_);
lean_dec(v_stx_5101_);
v___x_5149_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__2));
lean_inc(v___x_5148_);
v___x_5150_ = l_Lean_Syntax_isOfKind(v___x_5148_, v___x_5149_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; uint8_t v___x_5152_; 
v___x_5151_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5148_);
v___x_5152_ = l_Lean_Syntax_isOfKind(v___x_5148_, v___x_5151_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; 
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5153_;
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v_decl_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v___x_5154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5155_ = lean_unsigned_to_nat(1u);
v___x_5156_ = lean_mk_empty_array_with_capacity(v___x_5155_);
v___x_5157_ = lean_array_push(v___x_5156_, v___x_5148_);
v___x_5158_ = lean_box(2);
v_decl_5159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5159_, 0, v___x_5158_);
lean_ctor_set(v_decl_5159_, 1, v___x_5154_);
lean_ctor_set(v_decl_5159_, 2, v___x_5157_);
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5161_, 0, v___x_5160_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1, v___x_5150_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1 + 1, v___x_5150_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1 + 2, v___x_5150_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1 + 3, v___x_5150_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1 + 4, v___x_5150_);
v___x_5162_ = lean_box(2);
lean_inc_ref(v_decl_5159_);
v___x_5163_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5161_, v___x_5162_, v_decl_5159_, v_decl_5159_, v_dec_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
return v___x_5163_;
}
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; 
v___x_5164_ = l_Lean_Syntax_getArg(v___x_5148_, v___x_5147_);
v___x_5165_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5164_);
v___x_5166_ = l_Lean_Syntax_isOfKind(v___x_5164_, v___x_5165_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; 
lean_dec(v___x_5164_);
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5167_;
}
else
{
lean_object* v___x_5168_; lean_object* v_xType_x3f_5170_; lean_object* v___y_5171_; lean_object* v___y_5172_; lean_object* v___y_5173_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v___x_5197_; uint8_t v___x_5198_; 
v___x_5168_ = l_Lean_Syntax_getArg(v___x_5164_, v___x_5147_);
lean_dec(v___x_5164_);
v___x_5197_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5168_);
v___x_5198_ = l_Lean_Syntax_isOfKind(v___x_5168_, v___x_5197_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; 
lean_dec(v___x_5168_);
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5199_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5199_;
}
else
{
lean_object* v___x_5200_; lean_object* v___x_5201_; uint8_t v___x_5202_; 
v___x_5200_ = lean_unsigned_to_nat(1u);
v___x_5201_ = l_Lean_Syntax_getArg(v___x_5148_, v___x_5200_);
v___x_5202_ = l_Lean_Syntax_matchesNull(v___x_5201_, v___x_5147_);
if (v___x_5202_ == 0)
{
lean_object* v___x_5203_; 
lean_dec(v___x_5168_);
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5203_;
}
else
{
lean_object* v___x_5204_; lean_object* v___x_5205_; uint8_t v___x_5206_; 
v___x_5204_ = lean_unsigned_to_nat(2u);
v___x_5205_ = l_Lean_Syntax_getArg(v___x_5148_, v___x_5204_);
v___x_5206_ = l_Lean_Syntax_isNone(v___x_5205_);
if (v___x_5206_ == 0)
{
uint8_t v___x_5207_; 
lean_inc(v___x_5205_);
v___x_5207_ = l_Lean_Syntax_matchesNull(v___x_5205_, v___x_5200_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; 
lean_dec(v___x_5205_);
lean_dec(v___x_5168_);
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5208_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5208_;
}
else
{
lean_object* v___x_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; 
v___x_5209_ = l_Lean_Syntax_getArg(v___x_5205_, v___x_5147_);
lean_dec(v___x_5205_);
v___x_5210_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5209_);
v___x_5211_ = l_Lean_Syntax_isOfKind(v___x_5209_, v___x_5210_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; 
lean_dec(v___x_5209_);
lean_dec(v___x_5168_);
lean_dec(v___x_5148_);
lean_dec_ref(v_dec_5102_);
v___x_5212_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5212_;
}
else
{
lean_object* v_xType_x3f_5213_; lean_object* v___x_5214_; 
v_xType_x3f_5213_ = l_Lean_Syntax_getArg(v___x_5209_, v___x_5200_);
lean_dec(v___x_5209_);
v___x_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5214_, 0, v_xType_x3f_5213_);
v_xType_x3f_5170_ = v___x_5214_;
v___y_5171_ = v_a_5103_;
v___y_5172_ = v_a_5104_;
v___y_5173_ = v_a_5105_;
v___y_5174_ = v_a_5106_;
v___y_5175_ = v_a_5107_;
v___y_5176_ = v_a_5108_;
v___y_5177_ = v_a_5109_;
goto v___jp_5169_;
}
}
}
else
{
lean_object* v___x_5215_; 
lean_dec(v___x_5205_);
v___x_5215_ = lean_box(0);
v_xType_x3f_5170_ = v___x_5215_;
v___y_5171_ = v_a_5103_;
v___y_5172_ = v_a_5104_;
v___y_5173_ = v_a_5105_;
v___y_5174_ = v_a_5106_;
v___y_5175_ = v_a_5107_;
v___y_5176_ = v_a_5108_;
v___y_5177_ = v_a_5109_;
goto v___jp_5169_;
}
}
}
v___jp_5169_:
{
lean_object* v_ref_5178_; lean_object* v___x_5179_; lean_object* v_tk_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v_ref_5178_ = lean_ctor_get(v___y_5176_, 5);
v___x_5179_ = lean_unsigned_to_nat(3u);
v_tk_5180_ = l_Lean_Syntax_getArg(v___x_5148_, v___x_5179_);
v___x_5181_ = lean_unsigned_to_nat(4u);
v___x_5182_ = l_Lean_Syntax_getArg(v___x_5148_, v___x_5181_);
lean_dec(v___x_5148_);
v___x_5183_ = 0;
v___x_5184_ = l_Lean_SourceInfo_fromRef(v_ref_5178_, v___x_5183_);
v___x_5185_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5184_, 2);
v___x_5186_ = l_Lean_Syntax_node1(v___x_5184_, v___x_5165_, v___x_5168_);
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5188_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5184_);
lean_ctor_set(v___x_5189_, 1, v___x_5187_);
lean_ctor_set(v___x_5189_, 2, v___x_5188_);
if (lean_obj_tag(v_xType_x3f_5170_) == 1)
{
lean_object* v_val_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v_val_5190_ = lean_ctor_get(v_xType_x3f_5170_, 0);
lean_inc(v_val_5190_);
lean_dec_ref_known(v_xType_x3f_5170_, 1);
v___x_5191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5192_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5184_, 2);
v___x_5193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5184_);
lean_ctor_set(v___x_5193_, 1, v___x_5192_);
v___x_5194_ = l_Lean_Syntax_node2(v___x_5184_, v___x_5191_, v___x_5193_, v_val_5190_);
v___x_5195_ = l_Array_mkArray1___redArg(v___x_5194_);
v___y_5112_ = v___y_5174_;
v___y_5113_ = v___x_5184_;
v___y_5114_ = v___y_5177_;
v___y_5115_ = v___x_5188_;
v___y_5116_ = v___y_5175_;
v___y_5117_ = v___y_5172_;
v___y_5118_ = v___x_5186_;
v___y_5119_ = v___x_5183_;
v___y_5120_ = v___x_5189_;
v___y_5121_ = v___x_5185_;
v___y_5122_ = v_tk_5180_;
v___y_5123_ = v___x_5182_;
v___y_5124_ = v___y_5171_;
v___y_5125_ = v___y_5176_;
v___y_5126_ = v___x_5187_;
v___y_5127_ = v___y_5173_;
v___y_5128_ = v___x_5195_;
goto v___jp_5111_;
}
else
{
lean_object* v___x_5196_; 
lean_dec(v_xType_x3f_5170_);
v___x_5196_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__3));
v___y_5112_ = v___y_5174_;
v___y_5113_ = v___x_5184_;
v___y_5114_ = v___y_5177_;
v___y_5115_ = v___x_5188_;
v___y_5116_ = v___y_5175_;
v___y_5117_ = v___y_5172_;
v___y_5118_ = v___x_5186_;
v___y_5119_ = v___x_5183_;
v___y_5120_ = v___x_5189_;
v___y_5121_ = v___x_5185_;
v___y_5122_ = v_tk_5180_;
v___y_5123_ = v___x_5182_;
v___y_5124_ = v___y_5171_;
v___y_5125_ = v___y_5176_;
v___y_5126_ = v___x_5187_;
v___y_5127_ = v___y_5173_;
v___y_5128_ = v___x_5196_;
goto v___jp_5111_;
}
}
}
}
}
v___jp_5111_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
lean_inc_ref(v___y_5115_);
v___x_5129_ = l_Array_append___redArg(v___y_5115_, v___y_5128_);
lean_dec_ref(v___y_5128_);
lean_inc(v___y_5126_);
lean_inc_n(v___y_5113_, 2);
v___x_5130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5130_, 0, v___y_5113_);
lean_ctor_set(v___x_5130_, 1, v___y_5126_);
lean_ctor_set(v___x_5130_, 2, v___x_5129_);
v___x_5131_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5132_, 0, v___y_5113_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
lean_inc(v___y_5121_);
v___x_5133_ = l_Lean_Syntax_node5(v___y_5113_, v___y_5121_, v___y_5118_, v___y_5120_, v___x_5130_, v___x_5132_, v___y_5123_);
v___x_5134_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5135_ = lean_unsigned_to_nat(1u);
v___x_5136_ = lean_mk_empty_array_with_capacity(v___x_5135_);
v___x_5137_ = lean_array_push(v___x_5136_, v___x_5133_);
v___x_5138_ = lean_box(2);
v___x_5139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5138_);
lean_ctor_set(v___x_5139_, 1, v___x_5134_);
lean_ctor_set(v___x_5139_, 2, v___x_5137_);
v___x_5140_ = lean_box(0);
v___x_5141_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1, v___y_5119_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1 + 1, v___y_5119_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1 + 2, v___y_5119_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1 + 3, v___y_5119_);
lean_ctor_set_uint8(v___x_5141_, sizeof(void*)*1 + 4, v___y_5119_);
v___x_5142_ = lean_box(2);
v___x_5143_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5141_, v___x_5142_, v___x_5139_, v___y_5122_, v_dec_5102_, v___y_5124_, v___y_5117_, v___y_5127_, v___y_5112_, v___y_5116_, v___y_5125_, v___y_5114_);
return v___x_5143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5216_, lean_object* v_dec_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5216_, v_dec_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec_ref(v_a_5218_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5234_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5235_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__0));
v___x_5236_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5237_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5234_, v___x_5235_, v___x_5236_, v___x_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
uint8_t v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5250_ = 0;
v___x_5251_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5241_, v___x_5250_);
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v_____do__lift_5253_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5282_, size_t v_sz_5283_, size_t v_i_5284_, lean_object* v_b_5285_, lean_object* v___y_5286_){
_start:
{
uint8_t v___x_5288_; 
v___x_5288_ = lean_usize_dec_lt(v_i_5284_, v_sz_5283_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; 
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v_b_5285_);
return v___x_5289_;
}
else
{
lean_object* v_ref_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v_a_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; size_t v___x_5327_; size_t v___x_5328_; 
v_ref_5290_ = lean_ctor_get(v___y_5286_, 5);
v___x_5291_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5293_ = lean_array_uget_borrowed(v_as_5282_, v_i_5284_);
v___x_5294_ = 0;
v___x_5295_ = l_Lean_SourceInfo_fromRef(v_ref_5290_, v___x_5294_);
v___x_5296_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5298_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5299_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5295_, 17);
v___x_5300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5295_);
lean_ctor_set(v___x_5300_, 1, v___x_5299_);
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5295_);
lean_ctor_set(v___x_5302_, 1, v___x_5301_);
v___x_5303_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5296_, v___x_5302_);
v___x_5304_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5295_);
lean_ctor_set(v___x_5305_, 1, v___x_5296_);
lean_ctor_set(v___x_5305_, 2, v___x_5304_);
lean_inc_ref_n(v___x_5305_, 3);
v___x_5306_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5291_, v___x_5305_);
v___x_5307_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5308_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5309_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5293_, 2);
v___x_5310_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5309_, v_a_5293_);
v___x_5311_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5295_);
lean_ctor_set(v___x_5312_, 1, v___x_5311_);
v___x_5313_ = l_Lean_Syntax_node5(v___x_5295_, v___x_5308_, v___x_5310_, v___x_5305_, v___x_5305_, v___x_5312_, v_a_5293_);
v___x_5314_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5307_, v___x_5313_);
v___x_5315_ = l_Lean_Syntax_node4(v___x_5295_, v___x_5298_, v___x_5300_, v___x_5303_, v___x_5306_, v___x_5314_);
v___x_5316_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5295_);
lean_ctor_set(v___x_5317_, 1, v___x_5316_);
v___x_5318_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5296_, v___x_5317_);
v___x_5319_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5297_, v___x_5315_, v___x_5318_);
v___x_5320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5322_, 0, v___x_5295_);
lean_ctor_set(v___x_5322_, 1, v___x_5321_);
v___x_5323_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5320_, v___x_5322_, v_b_5285_);
v___x_5324_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5297_, v___x_5323_, v___x_5305_);
v___x_5325_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5296_, v___x_5319_, v___x_5324_);
v___x_5326_ = l_Lean_Syntax_node1(v___x_5295_, v___x_5292_, v___x_5325_);
v___x_5327_ = ((size_t)1ULL);
v___x_5328_ = lean_usize_add(v_i_5284_, v___x_5327_);
v_i_5284_ = v___x_5328_;
v_b_5285_ = v___x_5326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5330_, lean_object* v_sz_5331_, lean_object* v_i_5332_, lean_object* v_b_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
size_t v_sz_boxed_5336_; size_t v_i_boxed_5337_; lean_object* v_res_5338_; 
v_sz_boxed_5336_ = lean_unbox_usize(v_sz_5331_);
lean_dec(v_sz_5331_);
v_i_boxed_5337_ = lean_unbox_usize(v_i_5332_);
lean_dec(v_i_5332_);
v_res_5338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5330_, v_sz_boxed_5336_, v_i_boxed_5337_, v_b_5333_, v___y_5334_);
lean_dec_ref(v___y_5334_);
lean_dec_ref(v_as_5330_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5339_, size_t v_sz_5340_, size_t v_i_5341_, lean_object* v_b_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v___x_5351_; 
v___x_5351_ = lean_usize_dec_lt(v_i_5341_, v_sz_5340_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5352_, 0, v_b_5342_);
return v___x_5352_;
}
else
{
lean_object* v_ref_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v_a_5356_; uint8_t v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; size_t v___x_5390_; size_t v___x_5391_; lean_object* v___x_5392_; 
v_ref_5353_ = lean_ctor_get(v___y_5348_, 5);
v___x_5354_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v_a_5356_ = lean_array_uget_borrowed(v_as_5339_, v_i_5341_);
v___x_5357_ = 0;
v___x_5358_ = l_Lean_SourceInfo_fromRef(v_ref_5353_, v___x_5357_);
v___x_5359_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5361_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
v___x_5362_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5358_, 17);
v___x_5363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5358_);
lean_ctor_set(v___x_5363_, 1, v___x_5362_);
v___x_5364_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___lam__0___closed__5));
v___x_5365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5358_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
v___x_5366_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5359_, v___x_5365_);
v___x_5367_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5358_);
lean_ctor_set(v___x_5368_, 1, v___x_5359_);
lean_ctor_set(v___x_5368_, 2, v___x_5367_);
lean_inc_ref_n(v___x_5368_, 3);
v___x_5369_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5354_, v___x_5368_);
v___x_5370_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5371_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5372_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5356_, 2);
v___x_5373_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5372_, v_a_5356_);
v___x_5374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5358_);
lean_ctor_set(v___x_5375_, 1, v___x_5374_);
v___x_5376_ = l_Lean_Syntax_node5(v___x_5358_, v___x_5371_, v___x_5373_, v___x_5368_, v___x_5368_, v___x_5375_, v_a_5356_);
v___x_5377_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5370_, v___x_5376_);
v___x_5378_ = l_Lean_Syntax_node4(v___x_5358_, v___x_5361_, v___x_5363_, v___x_5366_, v___x_5369_, v___x_5377_);
v___x_5379_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__7));
v___x_5380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5358_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
v___x_5381_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5359_, v___x_5380_);
v___x_5382_ = l_Lean_Syntax_node2(v___x_5358_, v___x_5360_, v___x_5378_, v___x_5381_);
v___x_5383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__5));
v___x_5384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__6));
v___x_5385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5358_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
v___x_5386_ = l_Lean_Syntax_node2(v___x_5358_, v___x_5383_, v___x_5385_, v_b_5342_);
v___x_5387_ = l_Lean_Syntax_node2(v___x_5358_, v___x_5360_, v___x_5386_, v___x_5368_);
v___x_5388_ = l_Lean_Syntax_node2(v___x_5358_, v___x_5359_, v___x_5382_, v___x_5387_);
v___x_5389_ = l_Lean_Syntax_node1(v___x_5358_, v___x_5355_, v___x_5388_);
v___x_5390_ = ((size_t)1ULL);
v___x_5391_ = lean_usize_add(v_i_5341_, v___x_5390_);
v___x_5392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5339_, v_sz_5340_, v___x_5391_, v___x_5389_, v___y_5348_);
return v___x_5392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5393_, lean_object* v_sz_5394_, lean_object* v_i_5395_, lean_object* v_b_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
size_t v_sz_boxed_5405_; size_t v_i_boxed_5406_; lean_object* v_res_5407_; 
v_sz_boxed_5405_ = lean_unbox_usize(v_sz_5394_);
lean_dec(v_sz_5394_);
v_i_boxed_5406_ = lean_unbox_usize(v_i_5395_);
lean_dec(v_i_5395_);
v_res_5407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5393_, v_sz_boxed_5405_, v_i_boxed_5406_, v_b_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec_ref(v_as_5393_);
return v_res_5407_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5448_ = l_String_toRawSubstring_x27(v___x_5447_);
return v___x_5448_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5462_; lean_object* v___x_5463_; 
v___x_5462_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5463_ = l_String_toRawSubstring_x27(v___x_5462_);
return v___x_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5480_, lean_object* v_dec_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v___x_5490_; uint8_t v___x_5491_; 
v___x_5490_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
lean_inc(v_stx_5480_);
v___x_5491_ = l_Lean_Syntax_isOfKind(v_stx_5480_, v___x_5490_);
if (v___x_5491_ == 0)
{
lean_object* v___x_5492_; 
lean_dec_ref(v_dec_5481_);
lean_dec(v_stx_5480_);
v___x_5492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5492_;
}
else
{
lean_object* v___y_5494_; lean_object* v___y_5495_; uint8_t v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v_body_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; uint8_t v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; uint8_t v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v_a_5595_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; uint8_t v___y_5618_; lean_object* v___y_5619_; lean_object* v___y_5620_; lean_object* v___y_5621_; lean_object* v___y_5622_; lean_object* v_mutTk_x3f_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___x_5725_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v___x_5725_ = lean_unsigned_to_nat(1u);
v___x_5726_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5725_);
v___x_5727_ = l_Lean_Syntax_isNone(v___x_5726_);
if (v___x_5727_ == 0)
{
uint8_t v___x_5728_; 
lean_inc(v___x_5726_);
v___x_5728_ = l_Lean_Syntax_matchesNull(v___x_5726_, v___x_5725_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
lean_dec(v___x_5726_);
lean_dec_ref(v_dec_5481_);
lean_dec(v_stx_5480_);
v___x_5729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5729_;
}
else
{
lean_object* v___x_5730_; lean_object* v_mutTk_x3f_5731_; lean_object* v___x_5732_; 
v___x_5730_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5731_ = l_Lean_Syntax_getArg(v___x_5726_, v___x_5730_);
lean_dec(v___x_5726_);
v___x_5732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5732_, 0, v_mutTk_x3f_5731_);
v_mutTk_x3f_5694_ = v___x_5732_;
v___y_5695_ = v_a_5482_;
v___y_5696_ = v_a_5483_;
v___y_5697_ = v_a_5484_;
v___y_5698_ = v_a_5485_;
v___y_5699_ = v_a_5486_;
v___y_5700_ = v_a_5487_;
v___y_5701_ = v_a_5488_;
goto v___jp_5693_;
}
}
else
{
lean_object* v___x_5733_; 
lean_dec(v___x_5726_);
v___x_5733_ = lean_box(0);
v_mutTk_x3f_5694_ = v___x_5733_;
v___y_5695_ = v_a_5482_;
v___y_5696_ = v_a_5483_;
v___y_5697_ = v_a_5484_;
v___y_5698_ = v_a_5485_;
v___y_5699_ = v_a_5486_;
v___y_5700_ = v_a_5487_;
v___y_5701_ = v_a_5488_;
goto v___jp_5693_;
}
v___jp_5493_:
{
lean_object* v_eq_x3f_5507_; 
v_eq_x3f_5507_ = lean_ctor_get(v___y_5497_, 0);
lean_inc(v_eq_x3f_5507_);
lean_dec_ref(v___y_5497_);
if (lean_obj_tag(v_eq_x3f_5507_) == 1)
{
lean_object* v_val_5508_; lean_object* v_ref_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; 
v_val_5508_ = lean_ctor_get(v_eq_x3f_5507_, 0);
lean_inc(v_val_5508_);
lean_dec_ref_known(v_eq_x3f_5507_, 1);
v_ref_5509_ = lean_ctor_get(v___y_5505_, 5);
v___x_5510_ = l_Lean_SourceInfo_fromRef(v_ref_5509_, v___y_5496_);
v___x_5511_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5512_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
lean_inc_n(v___x_5510_, 19);
v___x_5513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5510_);
lean_ctor_set(v___x_5513_, 1, v___x_5512_);
v___x_5514_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5515_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5516_, 0, v___x_5510_);
lean_ctor_set(v___x_5516_, 1, v___x_5514_);
lean_ctor_set(v___x_5516_, 2, v___x_5515_);
v___x_5517_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5518_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5510_);
lean_ctor_set(v___x_5519_, 1, v___x_5518_);
v___x_5520_ = l_Lean_Syntax_node2(v___x_5510_, v___x_5514_, v_val_5508_, v___x_5519_);
v___x_5521_ = l_Lean_Syntax_node2(v___x_5510_, v___x_5517_, v___x_5520_, v___y_5498_);
v___x_5522_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5514_, v___x_5521_);
v___x_5523_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5510_);
lean_ctor_set(v___x_5524_, 1, v___x_5523_);
v___x_5525_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5527_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5510_);
lean_ctor_set(v___x_5528_, 1, v___x_5527_);
v___x_5529_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5514_, v___y_5495_);
v___x_5530_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5514_, v___x_5529_);
v___x_5531_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5510_);
lean_ctor_set(v___x_5532_, 1, v___x_5531_);
lean_inc_ref(v___x_5532_);
lean_inc_ref(v___x_5528_);
v___x_5533_ = l_Lean_Syntax_node4(v___x_5510_, v___x_5526_, v___x_5528_, v___x_5530_, v___x_5532_, v_body_5499_);
v___x_5534_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5535_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5536_, 0, v___x_5510_);
lean_ctor_set(v___x_5536_, 1, v___x_5535_);
v___x_5537_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5534_, v___x_5536_);
v___x_5538_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5514_, v___x_5537_);
v___x_5539_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5514_, v___x_5538_);
v___x_5540_ = l_Lean_Syntax_node4(v___x_5510_, v___x_5526_, v___x_5528_, v___x_5539_, v___x_5532_, v___y_5494_);
v___x_5541_ = l_Lean_Syntax_node2(v___x_5510_, v___x_5514_, v___x_5533_, v___x_5540_);
v___x_5542_ = l_Lean_Syntax_node1(v___x_5510_, v___x_5525_, v___x_5541_);
lean_inc_ref_n(v___x_5516_, 2);
v___x_5543_ = l_Lean_Syntax_node7(v___x_5510_, v___x_5511_, v___x_5513_, v___x_5516_, v___x_5516_, v___x_5516_, v___x_5522_, v___x_5524_, v___x_5542_);
v___x_5544_ = l_Lean_Elab_Do_elabDoElem(v___x_5543_, v_dec_5481_, v___x_5491_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
return v___x_5544_;
}
else
{
lean_object* v_ref_5545_; lean_object* v___x_5546_; lean_object* v_a_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
lean_dec(v_eq_x3f_5507_);
v_ref_5545_ = lean_ctor_get(v___y_5505_, 5);
v___x_5546_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5545_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
lean_inc_n(v_a_5547_, 18);
lean_dec_ref(v___x_5546_);
v___x_5548_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__2));
v___x_5549_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__10));
v___x_5550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5550_, 0, v_a_5547_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5552_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5553_, 0, v_a_5547_);
lean_ctor_set(v___x_5553_, 1, v___x_5551_);
lean_ctor_set(v___x_5553_, 2, v___x_5552_);
v___x_5554_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
lean_inc_ref_n(v___x_5553_, 3);
v___x_5555_ = l_Lean_Syntax_node2(v_a_5547_, v___x_5554_, v___x_5553_, v___y_5498_);
v___x_5556_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5551_, v___x_5555_);
v___x_5557_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__12));
v___x_5558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5558_, 0, v_a_5547_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v___x_5559_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5560_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5561_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__15));
v___x_5562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5562_, 0, v_a_5547_);
lean_ctor_set(v___x_5562_, 1, v___x_5561_);
v___x_5563_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5551_, v___y_5495_);
v___x_5564_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5551_, v___x_5563_);
v___x_5565_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__16));
v___x_5566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5566_, 0, v_a_5547_);
lean_ctor_set(v___x_5566_, 1, v___x_5565_);
lean_inc_ref(v___x_5566_);
lean_inc_ref(v___x_5562_);
v___x_5567_ = l_Lean_Syntax_node4(v_a_5547_, v___x_5560_, v___x_5562_, v___x_5564_, v___x_5566_, v_body_5499_);
v___x_5568_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__4));
v___x_5569_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__7___closed__21));
v___x_5570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5570_, 0, v_a_5547_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5568_, v___x_5570_);
v___x_5572_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5551_, v___x_5571_);
v___x_5573_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5551_, v___x_5572_);
v___x_5574_ = l_Lean_Syntax_node4(v_a_5547_, v___x_5560_, v___x_5562_, v___x_5573_, v___x_5566_, v___y_5494_);
v___x_5575_ = l_Lean_Syntax_node2(v_a_5547_, v___x_5551_, v___x_5567_, v___x_5574_);
v___x_5576_ = l_Lean_Syntax_node1(v_a_5547_, v___x_5559_, v___x_5575_);
v___x_5577_ = l_Lean_Syntax_node7(v_a_5547_, v___x_5548_, v___x_5550_, v___x_5553_, v___x_5553_, v___x_5553_, v___x_5556_, v___x_5558_, v___x_5576_);
v___x_5578_ = l_Lean_Elab_Do_elabDoElem(v___x_5577_, v_dec_5481_, v___x_5491_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
return v___x_5578_;
}
}
v___jp_5579_:
{
if (lean_obj_tag(v___y_5585_) == 0)
{
lean_dec_ref(v___y_5587_);
v___y_5494_ = v___y_5589_;
v___y_5495_ = v___y_5592_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5593_;
v___y_5498_ = v___y_5594_;
v_body_5499_ = v_a_5595_;
v___y_5500_ = v___y_5580_;
v___y_5501_ = v___y_5588_;
v___y_5502_ = v___y_5584_;
v___y_5503_ = v___y_5586_;
v___y_5504_ = v___y_5581_;
v___y_5505_ = v___y_5591_;
v___y_5506_ = v___y_5582_;
goto v___jp_5493_;
}
else
{
lean_dec_ref_known(v___y_5585_, 1);
if (v___y_5590_ == 0)
{
lean_dec_ref(v___y_5587_);
v___y_5494_ = v___y_5589_;
v___y_5495_ = v___y_5592_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5593_;
v___y_5498_ = v___y_5594_;
v_body_5499_ = v_a_5595_;
v___y_5500_ = v___y_5580_;
v___y_5501_ = v___y_5588_;
v___y_5502_ = v___y_5584_;
v___y_5503_ = v___y_5586_;
v___y_5504_ = v___y_5581_;
v___y_5505_ = v___y_5591_;
v___y_5506_ = v___y_5582_;
goto v___jp_5493_;
}
else
{
size_t v_sz_5596_; size_t v___x_5597_; lean_object* v___x_5598_; 
v_sz_5596_ = lean_array_size(v___y_5587_);
v___x_5597_ = ((size_t)0ULL);
v___x_5598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5587_, v_sz_5596_, v___x_5597_, v_a_5595_, v___y_5580_, v___y_5588_, v___y_5584_, v___y_5586_, v___y_5581_, v___y_5591_, v___y_5582_);
lean_dec_ref(v___y_5587_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_object* v_a_5599_; 
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
lean_inc(v_a_5599_);
lean_dec_ref_known(v___x_5598_, 1);
v___y_5494_ = v___y_5589_;
v___y_5495_ = v___y_5592_;
v___y_5496_ = v___y_5583_;
v___y_5497_ = v___y_5593_;
v___y_5498_ = v___y_5594_;
v_body_5499_ = v_a_5599_;
v___y_5500_ = v___y_5580_;
v___y_5501_ = v___y_5588_;
v___y_5502_ = v___y_5584_;
v___y_5503_ = v___y_5586_;
v___y_5504_ = v___y_5581_;
v___y_5505_ = v___y_5591_;
v___y_5506_ = v___y_5582_;
goto v___jp_5493_;
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v___y_5592_);
lean_dec(v___y_5589_);
lean_dec_ref(v_dec_5481_);
v_a_5600_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5598_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5598_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
}
}
v___jp_5608_:
{
uint8_t v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
v___x_5623_ = 0;
v___x_5624_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
v___x_5625_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v___y_5615_, v___y_5613_, v___x_5624_, v___y_5616_, v___y_5612_, v___y_5614_, v___y_5610_, v___y_5619_, v___y_5611_);
if (lean_obj_tag(v___x_5625_) == 0)
{
lean_object* v_a_5626_; lean_object* v___x_5627_; 
v_a_5626_ = lean_ctor_get(v___x_5625_, 0);
lean_inc(v_a_5626_);
lean_dec_ref_known(v___x_5625_, 1);
v___x_5627_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5626_, v___y_5609_, v___y_5616_, v___y_5612_, v___y_5614_, v___y_5610_, v___y_5619_, v___y_5611_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v___x_5628_; 
lean_dec_ref_known(v___x_5627_, 1);
lean_inc(v___y_5620_);
v___x_5628_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5620_, v___y_5616_, v___y_5612_, v___y_5614_, v___y_5610_, v___y_5619_, v___y_5611_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_a_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_a_5629_);
lean_dec_ref_known(v___x_5628_, 1);
lean_inc(v___y_5613_);
v___x_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5630_, 0, v___y_5613_);
v___x_5631_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5630_, v_a_5629_, v___y_5609_, v___y_5616_, v___y_5612_, v___y_5614_, v___y_5610_, v___y_5619_, v___y_5611_);
lean_dec_ref_known(v___x_5630_, 1);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_dec_ref_known(v___x_5631_, 1);
if (lean_obj_tag(v___y_5622_) == 0)
{
lean_object* v_ref_5632_; lean_object* v_quotContext_5633_; lean_object* v_currMacroScope_5634_; lean_object* v___x_5635_; lean_object* v_a_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v_ref_5632_ = lean_ctor_get(v___y_5619_, 5);
v_quotContext_5633_ = lean_ctor_get(v___y_5619_, 10);
v_currMacroScope_5634_ = lean_ctor_get(v___y_5619_, 11);
v___x_5635_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5632_, v___y_5609_, v___y_5616_, v___y_5612_, v___y_5614_, v___y_5610_, v___y_5619_, v___y_5611_);
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc_n(v_a_5636_, 9);
lean_dec_ref(v___x_5635_);
v___x_5637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__1));
v___x_5638_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___closed__3));
v___x_5640_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5642_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5634_, 2);
lean_inc_n(v_quotContext_5633_, 2);
v___x_5644_ = l_Lean_addMacroScope(v_quotContext_5633_, v___x_5643_, v_currMacroScope_5634_);
v___x_5645_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5646_, 0, v_a_5636_);
lean_ctor_set(v___x_5646_, 1, v___x_5642_);
lean_ctor_set(v___x_5646_, 2, v___x_5644_);
lean_ctor_set(v___x_5646_, 3, v___x_5645_);
v___x_5647_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5649_ = l_Lean_addMacroScope(v_quotContext_5633_, v___x_5648_, v_currMacroScope_5634_);
v___x_5650_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5651_, 0, v_a_5636_);
lean_ctor_set(v___x_5651_, 1, v___x_5647_);
lean_ctor_set(v___x_5651_, 2, v___x_5649_);
lean_ctor_set(v___x_5651_, 3, v___x_5650_);
v___x_5652_ = l_Lean_Syntax_node1(v_a_5636_, v___x_5638_, v___x_5651_);
v___x_5653_ = l_Lean_Syntax_node2(v_a_5636_, v___x_5641_, v___x_5646_, v___x_5652_);
v___x_5654_ = l_Lean_Syntax_node1(v_a_5636_, v___x_5640_, v___x_5653_);
v___x_5655_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5656_, 0, v_a_5636_);
lean_ctor_set(v___x_5656_, 1, v___x_5638_);
lean_ctor_set(v___x_5656_, 2, v___x_5655_);
v___x_5657_ = l_Lean_Syntax_node2(v_a_5636_, v___x_5639_, v___x_5654_, v___x_5656_);
v___x_5658_ = l_Lean_Syntax_node1(v_a_5636_, v___x_5638_, v___x_5657_);
v___x_5659_ = l_Lean_Syntax_node1(v_a_5636_, v___x_5637_, v___x_5658_);
v___y_5580_ = v___y_5609_;
v___y_5581_ = v___y_5610_;
v___y_5582_ = v___y_5611_;
v___y_5583_ = v___x_5623_;
v___y_5584_ = v___y_5612_;
v___y_5585_ = v___y_5613_;
v___y_5586_ = v___y_5614_;
v___y_5587_ = v_a_5629_;
v___y_5588_ = v___y_5616_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5618_;
v___y_5591_ = v___y_5619_;
v___y_5592_ = v___y_5620_;
v___y_5593_ = v_a_5626_;
v___y_5594_ = v___y_5621_;
v_a_5595_ = v___x_5659_;
goto v___jp_5579_;
}
else
{
lean_object* v_val_5660_; 
v_val_5660_ = lean_ctor_get(v___y_5622_, 0);
lean_inc(v_val_5660_);
lean_dec_ref_known(v___y_5622_, 1);
v___y_5580_ = v___y_5609_;
v___y_5581_ = v___y_5610_;
v___y_5582_ = v___y_5611_;
v___y_5583_ = v___x_5623_;
v___y_5584_ = v___y_5612_;
v___y_5585_ = v___y_5613_;
v___y_5586_ = v___y_5614_;
v___y_5587_ = v_a_5629_;
v___y_5588_ = v___y_5616_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5618_;
v___y_5591_ = v___y_5619_;
v___y_5592_ = v___y_5620_;
v___y_5593_ = v_a_5626_;
v___y_5594_ = v___y_5621_;
v_a_5595_ = v_val_5660_;
goto v___jp_5579_;
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
lean_dec(v_a_5629_);
lean_dec(v_a_5626_);
lean_dec(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec(v___y_5617_);
lean_dec(v___y_5613_);
lean_dec_ref(v_dec_5481_);
v_a_5661_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5631_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5631_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_dec(v_a_5626_);
lean_dec(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec(v___y_5617_);
lean_dec(v___y_5613_);
lean_dec_ref(v_dec_5481_);
v_a_5669_ = lean_ctor_get(v___x_5628_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5628_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5628_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5628_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
lean_dec(v_a_5626_);
lean_dec(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec(v___y_5617_);
lean_dec(v___y_5613_);
lean_dec_ref(v_dec_5481_);
v_a_5677_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5627_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5627_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
else
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5692_; 
lean_dec(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec(v___y_5617_);
lean_dec(v___y_5613_);
lean_dec_ref(v_dec_5481_);
v_a_5685_ = lean_ctor_get(v___x_5625_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5625_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5687_ = v___x_5625_;
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5625_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5685_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
v___jp_5693_:
{
lean_object* v___x_5702_; lean_object* v_cfg_5703_; lean_object* v___x_5704_; uint8_t v___x_5705_; 
v___x_5702_ = lean_unsigned_to_nat(2u);
v_cfg_5703_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5702_);
v___x_5704_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5703_);
v___x_5705_ = l_Lean_Syntax_isOfKind(v_cfg_5703_, v___x_5704_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; 
lean_dec(v_cfg_5703_);
lean_dec(v_mutTk_x3f_5694_);
lean_dec_ref(v_dec_5481_);
lean_dec(v_stx_5480_);
v___x_5706_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5706_;
}
else
{
lean_object* v___x_5707_; lean_object* v_pattern_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5707_ = lean_unsigned_to_nat(3u);
v_pattern_5708_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5707_);
v___x_5709_ = lean_unsigned_to_nat(5u);
v___x_5710_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5709_);
v___x_5711_ = lean_unsigned_to_nat(7u);
v___x_5712_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5711_);
v___x_5713_ = lean_unsigned_to_nat(8u);
v___x_5714_ = l_Lean_Syntax_getArg(v_stx_5480_, v___x_5713_);
lean_dec(v_stx_5480_);
v___x_5715_ = l_Lean_Syntax_getOptional_x3f(v___x_5714_);
lean_dec(v___x_5714_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v___x_5716_; 
v___x_5716_ = lean_box(0);
v___y_5609_ = v___y_5695_;
v___y_5610_ = v___y_5699_;
v___y_5611_ = v___y_5701_;
v___y_5612_ = v___y_5697_;
v___y_5613_ = v_mutTk_x3f_5694_;
v___y_5614_ = v___y_5698_;
v___y_5615_ = v_cfg_5703_;
v___y_5616_ = v___y_5696_;
v___y_5617_ = v___x_5712_;
v___y_5618_ = v___x_5705_;
v___y_5619_ = v___y_5700_;
v___y_5620_ = v_pattern_5708_;
v___y_5621_ = v___x_5710_;
v___y_5622_ = v___x_5716_;
goto v___jp_5608_;
}
else
{
lean_object* v_val_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5724_; 
v_val_5717_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5724_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5724_ == 0)
{
v___x_5719_ = v___x_5715_;
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_val_5717_);
lean_dec(v___x_5715_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5722_; 
if (v_isShared_5720_ == 0)
{
v___x_5722_ = v___x_5719_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_val_5717_);
v___x_5722_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
v___y_5609_ = v___y_5695_;
v___y_5610_ = v___y_5699_;
v___y_5611_ = v___y_5701_;
v___y_5612_ = v___y_5697_;
v___y_5613_ = v_mutTk_x3f_5694_;
v___y_5614_ = v___y_5698_;
v___y_5615_ = v_cfg_5703_;
v___y_5616_ = v___y_5696_;
v___y_5617_ = v___x_5712_;
v___y_5618_ = v___x_5705_;
v___y_5619_ = v___y_5700_;
v___y_5620_ = v_pattern_5708_;
v___y_5621_ = v___x_5710_;
v___y_5622_ = v___x_5722_;
goto v___jp_5608_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5734_, lean_object* v_dec_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5734_, v_dec_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
lean_dec(v_a_5742_);
lean_dec_ref(v_a_5741_);
lean_dec(v_a_5740_);
lean_dec_ref(v_a_5739_);
lean_dec(v_a_5738_);
lean_dec_ref(v_a_5737_);
lean_dec_ref(v_a_5736_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5745_, size_t v_sz_5746_, size_t v_i_5747_, lean_object* v_b_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5745_, v_sz_5746_, v_i_5747_, v_b_5748_, v___y_5754_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5758_, lean_object* v_sz_5759_, lean_object* v_i_5760_, lean_object* v_b_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_){
_start:
{
size_t v_sz_boxed_5770_; size_t v_i_boxed_5771_; lean_object* v_res_5772_; 
v_sz_boxed_5770_ = lean_unbox_usize(v_sz_5759_);
lean_dec(v_sz_5759_);
v_i_boxed_5771_ = lean_unbox_usize(v_i_5760_);
lean_dec(v_i_5760_);
v_res_5772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5758_, v_sz_boxed_5770_, v_i_boxed_5771_, v_b_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec_ref(v_as_5758_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5780_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5781_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5782_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5783_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5784_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5780_, v___x_5781_, v___x_5782_, v___x_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5785_){
_start:
{
lean_object* v_res_5786_; 
v_res_5786_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5786_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3(void){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__2));
v___x_5795_ = l_Lean_stringToMessageData(v___x_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5796_, lean_object* v_dec_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_){
_start:
{
lean_object* v___x_5806_; uint8_t v___x_5807_; 
v___x_5806_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
lean_inc(v_stx_5796_);
v___x_5807_ = l_Lean_Syntax_isOfKind(v_stx_5796_, v___x_5806_);
if (v___x_5807_ == 0)
{
lean_object* v___x_5808_; 
lean_dec_ref(v_dec_5797_);
lean_dec(v_stx_5796_);
v___x_5808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5808_;
}
else
{
lean_object* v___x_5809_; lean_object* v_tk_5810_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5833_; lean_object* v___y_5845_; lean_object* v___y_5846_; lean_object* v___y_5847_; uint8_t v___y_5848_; lean_object* v___y_5849_; lean_object* v___y_5850_; lean_object* v___y_5851_; lean_object* v___y_5852_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; uint8_t v___y_5857_; lean_object* v___y_5860_; lean_object* v___y_5861_; lean_object* v___y_5862_; uint8_t v___y_5863_; lean_object* v___y_5864_; lean_object* v___y_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; uint8_t v___y_5872_; lean_object* v_mutTk_x3f_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___y_5880_; lean_object* v___y_5881_; lean_object* v___y_5882_; lean_object* v___x_5912_; lean_object* v___x_5913_; uint8_t v___x_5914_; 
v___x_5809_ = lean_unsigned_to_nat(0u);
v_tk_5810_ = l_Lean_Syntax_getArg(v_stx_5796_, v___x_5809_);
v___x_5912_ = lean_unsigned_to_nat(1u);
v___x_5913_ = l_Lean_Syntax_getArg(v_stx_5796_, v___x_5912_);
v___x_5914_ = l_Lean_Syntax_isNone(v___x_5913_);
if (v___x_5914_ == 0)
{
uint8_t v___x_5915_; 
lean_inc(v___x_5913_);
v___x_5915_ = l_Lean_Syntax_matchesNull(v___x_5913_, v___x_5912_);
if (v___x_5915_ == 0)
{
lean_object* v___x_5916_; 
lean_dec(v___x_5913_);
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
lean_dec(v_stx_5796_);
v___x_5916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5916_;
}
else
{
lean_object* v_mutTk_x3f_5917_; lean_object* v___x_5918_; 
v_mutTk_x3f_5917_ = l_Lean_Syntax_getArg(v___x_5913_, v___x_5809_);
lean_dec(v___x_5913_);
v___x_5918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5918_, 0, v_mutTk_x3f_5917_);
v_mutTk_x3f_5875_ = v___x_5918_;
v___y_5876_ = v_a_5798_;
v___y_5877_ = v_a_5799_;
v___y_5878_ = v_a_5800_;
v___y_5879_ = v_a_5801_;
v___y_5880_ = v_a_5802_;
v___y_5881_ = v_a_5803_;
v___y_5882_ = v_a_5804_;
goto v___jp_5874_;
}
}
else
{
lean_object* v___x_5919_; 
lean_dec(v___x_5913_);
v___x_5919_ = lean_box(0);
v_mutTk_x3f_5875_ = v___x_5919_;
v___y_5876_ = v_a_5798_;
v___y_5877_ = v_a_5799_;
v___y_5878_ = v_a_5800_;
v___y_5879_ = v_a_5801_;
v___y_5880_ = v_a_5802_;
v___y_5881_ = v_a_5803_;
v___y_5882_ = v_a_5804_;
goto v___jp_5874_;
}
v___jp_5811_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5821_, 0, v___y_5812_);
v___x_5822_ = l_Lean_Elab_Do_elabDoArrow(v___x_5821_, v___y_5813_, v_tk_5810_, v_dec_5797_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v_tk_5810_);
return v___x_5822_;
}
v___jp_5823_:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec(v___y_5831_);
lean_dec(v___y_5830_);
v___x_5834_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__3, &l_Lean_Elab_Do_elabDoLetArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__3);
v___x_5835_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__9_spec__16___redArg(v___y_5829_, v___x_5834_, v___y_5826_, v___y_5825_, v___y_5828_, v___y_5827_);
lean_dec(v___y_5829_);
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5835_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5835_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
v___jp_5844_:
{
if (v___y_5857_ == 0)
{
lean_object* v_eq_x3f_5858_; 
v_eq_x3f_5858_ = lean_ctor_get(v___y_5849_, 0);
lean_inc(v_eq_x3f_5858_);
lean_dec_ref(v___y_5849_);
if (lean_obj_tag(v_eq_x3f_5858_) == 0)
{
lean_dec(v___y_5854_);
v___y_5812_ = v___y_5855_;
v___y_5813_ = v___y_5847_;
v___y_5814_ = v___y_5856_;
v___y_5815_ = v___y_5850_;
v___y_5816_ = v___y_5845_;
v___y_5817_ = v___y_5851_;
v___y_5818_ = v___y_5852_;
v___y_5819_ = v___y_5853_;
v___y_5820_ = v___y_5846_;
goto v___jp_5811_;
}
else
{
lean_dec_ref_known(v_eq_x3f_5858_, 1);
if (v___y_5848_ == 0)
{
lean_dec(v___y_5854_);
v___y_5812_ = v___y_5855_;
v___y_5813_ = v___y_5847_;
v___y_5814_ = v___y_5856_;
v___y_5815_ = v___y_5850_;
v___y_5816_ = v___y_5845_;
v___y_5817_ = v___y_5851_;
v___y_5818_ = v___y_5852_;
v___y_5819_ = v___y_5853_;
v___y_5820_ = v___y_5846_;
goto v___jp_5811_;
}
else
{
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
v___y_5824_ = v___y_5845_;
v___y_5825_ = v___y_5852_;
v___y_5826_ = v___y_5851_;
v___y_5827_ = v___y_5846_;
v___y_5828_ = v___y_5853_;
v___y_5829_ = v___y_5854_;
v___y_5830_ = v___y_5855_;
v___y_5831_ = v___y_5847_;
v___y_5832_ = v___y_5856_;
v___y_5833_ = v___y_5850_;
goto v___jp_5823_;
}
}
}
else
{
lean_dec_ref(v___y_5849_);
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
v___y_5824_ = v___y_5845_;
v___y_5825_ = v___y_5852_;
v___y_5826_ = v___y_5851_;
v___y_5827_ = v___y_5846_;
v___y_5828_ = v___y_5853_;
v___y_5829_ = v___y_5854_;
v___y_5830_ = v___y_5855_;
v___y_5831_ = v___y_5847_;
v___y_5832_ = v___y_5856_;
v___y_5833_ = v___y_5850_;
goto v___jp_5823_;
}
}
v___jp_5859_:
{
if (v___y_5872_ == 0)
{
uint8_t v_zeta_5873_; 
v_zeta_5873_ = lean_ctor_get_uint8(v___y_5864_, sizeof(void*)*1 + 2);
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
v___y_5856_ = v___y_5871_;
v___y_5857_ = v_zeta_5873_;
goto v___jp_5844_;
}
else
{
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
v___y_5856_ = v___y_5871_;
v___y_5857_ = v___x_5807_;
goto v___jp_5844_;
}
}
v___jp_5874_:
{
lean_object* v___x_5883_; lean_object* v_cfg_5884_; lean_object* v___x_5885_; uint8_t v___x_5886_; 
v___x_5883_ = lean_unsigned_to_nat(2u);
v_cfg_5884_ = l_Lean_Syntax_getArg(v_stx_5796_, v___x_5883_);
v___x_5885_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_cfg_5884_);
v___x_5886_ = l_Lean_Syntax_isOfKind(v_cfg_5884_, v___x_5885_);
if (v___x_5886_ == 0)
{
lean_object* v___x_5887_; 
lean_dec(v_cfg_5884_);
lean_dec(v_mutTk_x3f_5875_);
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
lean_dec(v_stx_5796_);
v___x_5887_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5887_;
}
else
{
lean_object* v___x_5888_; lean_object* v___x_5889_; 
v___x_5888_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__2));
lean_inc(v_cfg_5884_);
v___x_5889_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___redArg(v_cfg_5884_, v_mutTk_x3f_5875_, v___x_5888_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
if (lean_obj_tag(v___x_5889_) == 0)
{
lean_object* v_a_5890_; lean_object* v___x_5891_; 
v_a_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5890_);
lean_dec_ref_known(v___x_5889_, 1);
v___x_5891_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_a_5890_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
if (lean_obj_tag(v___x_5891_) == 0)
{
uint8_t v_nondep_5892_; uint8_t v_usedOnly_5893_; lean_object* v___x_5894_; lean_object* v_decl_5895_; 
lean_dec_ref_known(v___x_5891_, 1);
v_nondep_5892_ = lean_ctor_get_uint8(v_a_5890_, sizeof(void*)*1);
v_usedOnly_5893_ = lean_ctor_get_uint8(v_a_5890_, sizeof(void*)*1 + 1);
v___x_5894_ = lean_unsigned_to_nat(3u);
v_decl_5895_ = l_Lean_Syntax_getArg(v_stx_5796_, v___x_5894_);
lean_dec(v_stx_5796_);
if (v_nondep_5892_ == 0)
{
v___y_5860_ = v___y_5878_;
v___y_5861_ = v___y_5882_;
v___y_5862_ = v_decl_5895_;
v___y_5863_ = v___x_5886_;
v___y_5864_ = v_a_5890_;
v___y_5865_ = v___y_5877_;
v___y_5866_ = v___y_5879_;
v___y_5867_ = v___y_5880_;
v___y_5868_ = v___y_5881_;
v___y_5869_ = v_cfg_5884_;
v___y_5870_ = v_mutTk_x3f_5875_;
v___y_5871_ = v___y_5876_;
v___y_5872_ = v_usedOnly_5893_;
goto v___jp_5859_;
}
else
{
v___y_5860_ = v___y_5878_;
v___y_5861_ = v___y_5882_;
v___y_5862_ = v_decl_5895_;
v___y_5863_ = v___x_5886_;
v___y_5864_ = v_a_5890_;
v___y_5865_ = v___y_5877_;
v___y_5866_ = v___y_5879_;
v___y_5867_ = v___y_5880_;
v___y_5868_ = v___y_5881_;
v___y_5869_ = v_cfg_5884_;
v___y_5870_ = v_mutTk_x3f_5875_;
v___y_5871_ = v___y_5876_;
v___y_5872_ = v___x_5807_;
goto v___jp_5859_;
}
}
else
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5903_; 
lean_dec(v_a_5890_);
lean_dec(v_cfg_5884_);
lean_dec(v_mutTk_x3f_5875_);
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
lean_dec(v_stx_5796_);
v_a_5896_ = lean_ctor_get(v___x_5891_, 0);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5891_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5898_ = v___x_5891_;
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5891_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5901_; 
if (v_isShared_5899_ == 0)
{
v___x_5901_ = v___x_5898_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
v___x_5901_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
return v___x_5901_;
}
}
}
}
else
{
lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5911_; 
lean_dec(v_cfg_5884_);
lean_dec(v_mutTk_x3f_5875_);
lean_dec(v_tk_5810_);
lean_dec_ref(v_dec_5797_);
lean_dec(v_stx_5796_);
v_a_5904_ = lean_ctor_get(v___x_5889_, 0);
v_isSharedCheck_5911_ = !lean_is_exclusive(v___x_5889_);
if (v_isSharedCheck_5911_ == 0)
{
v___x_5906_ = v___x_5889_;
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5889_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v___x_5909_; 
if (v_isShared_5907_ == 0)
{
v___x_5909_ = v___x_5906_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_a_5904_);
v___x_5909_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
return v___x_5909_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_5920_, lean_object* v_dec_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_){
_start:
{
lean_object* v_res_5930_; 
v_res_5930_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_5920_, v_dec_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_);
lean_dec(v_a_5928_);
lean_dec_ref(v_a_5927_);
lean_dec(v_a_5926_);
lean_dec_ref(v_a_5925_);
lean_dec(v_a_5924_);
lean_dec_ref(v_a_5923_);
lean_dec_ref(v_a_5922_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; 
v___x_5938_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5939_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__1));
v___x_5940_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_5941_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_5942_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5938_, v___x_5939_, v___x_5940_, v___x_5941_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_5943_){
_start:
{
lean_object* v_res_5944_; 
v_res_5944_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_5944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_5951_, lean_object* v_dec_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_5951_);
v___x_5962_ = l_Lean_Syntax_isOfKind(v_stx_5951_, v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; 
lean_dec_ref(v_dec_5952_);
lean_dec(v_stx_5951_);
v___x_5963_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5963_;
}
else
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; uint8_t v___x_5967_; 
v___x_5964_ = lean_unsigned_to_nat(0u);
v___x_5965_ = l_Lean_Syntax_getArg(v_stx_5951_, v___x_5964_);
lean_dec(v_stx_5951_);
v___x_5966_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__1));
lean_inc(v___x_5965_);
v___x_5967_ = l_Lean_Syntax_isOfKind(v___x_5965_, v___x_5966_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; uint8_t v___x_5969_; 
v___x_5968_ = ((lean_object*)(l_Lean_Elab_Do_elabDoArrow___closed__3));
lean_inc(v___x_5965_);
v___x_5969_ = l_Lean_Syntax_isOfKind(v___x_5965_, v___x_5968_);
if (v___x_5969_ == 0)
{
lean_object* v___x_5970_; 
lean_dec(v___x_5965_);
lean_dec_ref(v_dec_5952_);
v___x_5970_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___redArg();
return v___x_5970_;
}
else
{
lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5971_ = lean_box(2);
lean_inc(v___x_5965_);
v___x_5972_ = l_Lean_Elab_Do_elabDoArrow(v___x_5971_, v___x_5965_, v___x_5965_, v_dec_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
lean_dec(v___x_5965_);
return v___x_5972_;
}
}
else
{
lean_object* v___x_5973_; lean_object* v___x_5974_; 
v___x_5973_ = lean_box(2);
lean_inc(v___x_5965_);
v___x_5974_ = l_Lean_Elab_Do_elabDoArrow(v___x_5973_, v___x_5965_, v___x_5965_, v_dec_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
lean_dec(v___x_5965_);
return v___x_5974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_5975_, lean_object* v_dec_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_5975_, v_dec_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
lean_dec(v_a_5983_);
lean_dec_ref(v_a_5982_);
lean_dec(v_a_5981_);
lean_dec_ref(v_a_5980_);
lean_dec(v_a_5979_);
lean_dec_ref(v_a_5978_);
lean_dec_ref(v_a_5977_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5993_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5994_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_5995_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_5996_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_5997_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5993_, v___x_5994_, v___x_5995_, v___x_5996_);
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_5998_){
_start:
{
lean_object* v_res_5999_; 
v_res_5999_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_5999_;
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
