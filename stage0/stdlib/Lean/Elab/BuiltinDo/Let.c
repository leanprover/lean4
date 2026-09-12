// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Let
// Imports: meta import Init.Data.Erased public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.BuiltinDo.Basic import Lean.Elab.Do.PatternVar
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
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_withErasedProj(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Elab_Do_registerMutVarAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_findMutVar_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Do_declareMutVars_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Elab_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_throwUnlessMutVarsDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withPushMacroExpansionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_LocalDeclKind_ofBinderName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_mkLetIdDeclView(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Do_getLetRecDeclsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_Do_declareMutVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_throwUnlessMutVarDeclared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Do_LetOrReassign_isErasedDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_isErasedDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "an erased variable takes a plain reassignment, as in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " := e`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "`+generalize` is not supported in `do` blocks"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`+postponeValue` is not supported in `do` blocks"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Erased.mk"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Erased"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 6, 0, 4, 37, 246, 41)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(74, 35, 74, 233, 12, 85, 169, 163)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 6, 0, 4, 37, 246, 41)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__11_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__13_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__30_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__27_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__16_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "let_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "waitIfTypeMVar"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "wait_if_type_mvar%"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object**);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__12_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "let body of "};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__1;
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
static const lean_string_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letEqnsDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__9_value),LEAN_SCALAR_PTR_LITERAL(82, 210, 72, 51, 179, 245, 26, 94)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "configuration options are not allowed with `let mut`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Do_elabDoLet___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLet___closed__4_value;
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
static const lean_string_object l_Lean_Elab_Do_elabDoErased___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doErased"};
static const lean_object* l_Lean_Elab_Do_elabDoErased___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 69, 120, 16, 133, 86, 56, 26)}};
static const lean_object* l_Lean_Elab_Do_elabDoErased___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__1_value;
static const lean_array_object l_Lean_Elab_Do_elabDoErased___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoErased___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoErased___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_elabDoErased___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoErased___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_elabDoErased___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoErased___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoErased"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 19, 50, 139, 19, 74, 58, 104)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__5_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doErasedArrow"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(176, 216, 203, 158, 108, 103, 134, 112)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "erased"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mut"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__x"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__12 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__12_value),LEAN_SCALAR_PTR_LITERAL(238, 215, 60, 46, 39, 217, 189, 106)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_expandDoErasedArrow___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_expandDoErasedArrow___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoErasedArrow___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expandDoErasedArrow"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 145, 84, 137, 209, 6, 18, 127)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_elabDoHave___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_elabDoHave___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoHave___closed__1_value;
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
static const lean_string_object l_Lean_Elab_Do_elabDoReassign___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoReassign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_elabDoReassign___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassign___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoLetElse___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_elabDoLetElse___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetElse___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetElse___closed__8_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 48, .m_data = "configuration options are not supported with `←`"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoLetArrow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__1;
static const lean_string_object l_Lean_Elab_Do_elabDoLetArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoLetArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_elabDoLetArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoLetArrow___closed__3_value;
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
static const lean_string_object l_Lean_Elab_Do_elabDoReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "reassignment with `|` (i.e., \"else clause\") is not supported"};
static const lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoReassignArrow___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoReassignArrow___closed__3;
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
lean_object* v_mutTk_x3f_9_; uint8_t v_erased_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_mutTk_x3f_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_mutTk_x3f_9_);
v_erased_10_ = lean_ctor_get_uint8(v_t_7_, sizeof(void*)*1);
lean_dec_ref_known(v_t_7_, 1);
v___x_11_ = lean_box(v_erased_10_);
v___x_12_ = lean_apply_2(v_k_8_, v_mutTk_x3f_9_, v___x_11_);
return v___x_12_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Do_LetOrReassign_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim___redArg(lean_object* v_t_25_, lean_object* v_let_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_25_, v_let_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_let_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_let_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_29_, v_let_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim___redArg(lean_object* v_t_33_, lean_object* v_have_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_33_, v_have_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_have_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_have_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_37_, v_have_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim___redArg(lean_object* v_t_41_, lean_object* v_reassign_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_41_, v_reassign_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_reassign_elim(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_reassign_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Elab_Do_LetOrReassign_ctorElim___redArg(v_t_45_, v_reassign_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(lean_object* v_letOrReassign_49_){
_start:
{
if (lean_obj_tag(v_letOrReassign_49_) == 0)
{
lean_object* v_mutTk_x3f_50_; 
v_mutTk_x3f_50_ = lean_ctor_get(v_letOrReassign_49_, 0);
lean_inc(v_mutTk_x3f_50_);
return v_mutTk_x3f_50_;
}
else
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(0);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f___boxed(lean_object* v_letOrReassign_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_52_);
lean_dec(v_letOrReassign_52_);
return v_res_53_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Do_LetOrReassign_isErasedDecl(lean_object* v_letOrReassign_54_){
_start:
{
if (lean_obj_tag(v_letOrReassign_54_) == 0)
{
uint8_t v_erased_55_; 
v_erased_55_ = lean_ctor_get_uint8(v_letOrReassign_54_, sizeof(void*)*1);
return v_erased_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_isErasedDecl___boxed(lean_object* v_letOrReassign_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_Elab_Do_LetOrReassign_isErasedDecl(v_letOrReassign_57_);
lean_dec(v_letOrReassign_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg(lean_object* v_letOrReassign_60_, lean_object* v_vars_61_, lean_object* v_a_62_){
_start:
{
switch(lean_obj_tag(v_letOrReassign_60_))
{
case 0:
{
uint8_t v_erased_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_erased_64_ = lean_ctor_get_uint8(v_letOrReassign_60_, sizeof(void*)*1);
v___x_65_ = lean_box(v_erased_64_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
case 2:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_array_get_size(v_vars_61_);
v___x_69_ = lean_nat_dec_lt(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_box(v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_array_fget_borrowed(v_vars_61_, v___x_67_);
v___x_73_ = l_Lean_TSyntax_getId(v___x_72_);
v___x_74_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_73_, v_a_62_);
lean_dec(v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_90_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_90_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_90_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_90_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
if (lean_obj_tag(v_a_75_) == 1)
{
lean_object* v_val_79_; uint8_t v_erased_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v_val_79_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_val_79_);
lean_dec_ref_known(v_a_75_, 1);
v_erased_80_ = lean_ctor_get_uint8(v_val_79_, sizeof(void*)*2);
lean_dec(v_val_79_);
v___x_81_ = lean_box(v_erased_80_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_81_);
v___x_83_ = v___x_77_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec(v_a_75_);
v___x_85_ = 0;
v___x_86_ = lean_box(v___x_85_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_86_);
v___x_88_ = v___x_77_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_a_91_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_74_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_74_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
default: 
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 0;
v___x_100_ = lean_box(v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___redArg___boxed(lean_object* v_letOrReassign_102_, lean_object* v_vars_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_102_, v_vars_103_, v_a_104_);
lean_dec_ref(v_a_104_);
lean_dec_ref(v_vars_103_);
lean_dec(v_letOrReassign_102_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased(lean_object* v_letOrReassign_107_, lean_object* v_vars_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_107_, v_vars_108_, v_a_109_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_isErased___boxed(lean_object* v_letOrReassign_118_, lean_object* v_vars_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Elab_Do_isErased(v_letOrReassign_118_, v_vars_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec_ref(v_vars_119_);
lean_dec(v_letOrReassign_118_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(lean_object* v_msgData_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v_env_136_; lean_object* v___x_137_; lean_object* v_toCold_138_; lean_object* v_mctx_139_; lean_object* v_lctx_140_; lean_object* v_options_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_135_ = lean_st_ref_get(v___y_133_);
v_env_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_env_136_);
lean_dec(v___x_135_);
v___x_137_ = lean_st_ref_get(v___y_131_);
v_toCold_138_ = lean_ctor_get(v___y_132_, 0);
v_mctx_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_mctx_139_);
lean_dec(v___x_137_);
v_lctx_140_ = lean_ctor_get(v___y_130_, 2);
v_options_141_ = lean_ctor_get(v_toCold_138_, 2);
lean_inc_ref(v_options_141_);
lean_inc_ref(v_lctx_140_);
v___x_142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_142_, 0, v_env_136_);
lean_ctor_set(v___x_142_, 1, v_mctx_139_);
lean_ctor_set(v___x_142_, 2, v_lctx_140_);
lean_ctor_set(v___x_142_, 3, v_options_141_);
v___x_143_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_msgData_129_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msgData_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(lean_object* v_msg_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_ref_158_; lean_object* v___x_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_ref_158_ = lean_ctor_get(v___y_155_, 2);
v___x_159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_inc(v_ref_158_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_ref_158_);
lean_ctor_set(v___x_164_, 1, v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set_tag(v___x_162_, 1);
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg___boxed(lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(lean_object* v_ref_176_, lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_toCold_186_; lean_object* v_currRecDepth_187_; lean_object* v_ref_188_; uint8_t v_diag_189_; uint8_t v_suppressElabErrors_190_; lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_toCold_186_ = lean_ctor_get(v___y_183_, 0);
v_currRecDepth_187_ = lean_ctor_get(v___y_183_, 1);
v_ref_188_ = lean_ctor_get(v___y_183_, 2);
v_diag_189_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3);
v_suppressElabErrors_190_ = lean_ctor_get_uint8(v___y_183_, sizeof(void*)*3 + 1);
v_ref_191_ = l_Lean_replaceRef(v_ref_176_, v_ref_188_);
lean_inc(v_currRecDepth_187_);
lean_inc_ref(v_toCold_186_);
v___x_192_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_192_, 0, v_toCold_186_);
lean_ctor_set(v___x_192_, 1, v_currRecDepth_187_);
lean_ctor_set(v___x_192_, 2, v_ref_191_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*3, v_diag_189_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*3 + 1, v_suppressElabErrors_190_);
v___x_193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_177_, v___y_181_, v___y_182_, v___x_192_, v___y_184_);
lean_dec_ref_known(v___x_192_, 3);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg___boxed(lean_object* v_ref_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_194_, v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v_ref_194_);
return v_res_204_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__0));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__2));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(lean_object* v_as_211_, size_t v_sz_212_, size_t v_i_213_, lean_object* v_b_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_a_224_; uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_213_, v_sz_212_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_b_214_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v_a_231_ = lean_array_uget_borrowed(v_as_211_, v_i_213_);
v___x_232_ = l_Lean_TSyntax_getId(v_a_231_);
v___x_233_ = l_Lean_Elab_Do_findMutVar_x3f___redArg(v___x_232_, v___y_215_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
if (lean_obj_tag(v_a_234_) == 0)
{
lean_dec(v___x_232_);
v_a_224_ = v___x_230_;
goto v___jp_223_;
}
else
{
lean_object* v_val_235_; uint8_t v_erased_236_; 
v_val_235_ = lean_ctor_get(v_a_234_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_a_234_, 1);
v_erased_236_ = lean_ctor_get_uint8(v_val_235_, sizeof(void*)*2);
lean_dec(v_val_235_);
if (v_erased_236_ == 0)
{
lean_dec(v___x_232_);
v_a_224_ = v___x_230_;
goto v___jp_223_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_237_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__1);
v___x_238_ = l_Lean_MessageData_ofName(v___x_232_);
v___x_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___closed__3);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_231_, v___x_241_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_dec_ref_known(v___x_242_, 1);
v_a_224_ = v___x_230_;
goto v___jp_223_;
}
else
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v___x_232_);
v_a_243_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_233_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_233_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
v___jp_223_:
{
size_t v___x_225_; size_t v___x_226_; 
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_213_, v___x_225_);
v_i_213_ = v___x_226_;
v_b_214_ = v_a_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1___boxed(lean_object* v_as_251_, lean_object* v_sz_252_, lean_object* v_i_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_252_);
lean_dec(v_sz_252_);
v_i_boxed_264_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_as_251_, v_sz_boxed_263_, v_i_boxed_264_, v_b_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_as_251_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars(lean_object* v_letOrReassign_266_, lean_object* v_vars_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
if (lean_obj_tag(v_letOrReassign_266_) == 2)
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Elab_Do_throwUnlessMutVarsDeclared(v_vars_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_299_; 
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_300_);
v___x_278_ = v___x_276_;
v_isShared_279_ = v_isSharedCheck_299_;
goto v_resetjp_277_;
}
else
{
lean_dec(v___x_276_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_299_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_array_get_size(v_vars_267_);
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_dec_eq(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; size_t v_sz_284_; size_t v___x_285_; lean_object* v___x_286_; 
lean_del_object(v___x_278_);
v___x_283_ = lean_box(0);
v_sz_284_ = lean_array_size(v_vars_267_);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__1(v_vars_267_, v_sz_284_, v___x_285_, v___x_283_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v___x_286_, 0);
lean_dec(v_unused_294_);
v___x_288_ = v___x_286_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_286_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_283_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_283_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
return v___x_286_;
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_295_);
v___x_297_ = v___x_278_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
return v___x_276_;
}
}
else
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v_vars_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_checkMutVars___boxed(lean_object* v_letOrReassign_302_, lean_object* v_vars_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_302_, v_vars_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec_ref(v_vars_303_);
lean_dec(v_letOrReassign_302_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(lean_object* v_00_u03b1_313_, lean_object* v_ref_314_, lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_ref_314_, v_msg_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___boxed(lean_object* v_00_u03b1_325_, lean_object* v_ref_326_, lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0(v_00_u03b1_325_, v_ref_326_, v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v_ref_326_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(lean_object* v_00_u03b1_337_, lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v_msg_338_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___boxed(lean_object* v_00_u03b1_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0(v_00_u03b1_348_, v_msg_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(lean_object* v_as_359_, size_t v_sz_360_, size_t v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_lt(v_i_361_, v_sz_360_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_b_362_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_box(0);
v_a_374_ = lean_array_uget_borrowed(v_as_359_, v_i_361_);
v___x_375_ = l_Lean_TSyntax_getId(v_a_374_);
v___x_376_ = l_Lean_Elab_Do_registerMutVarAlias(v___x_375_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_376_) == 0)
{
size_t v___x_377_; size_t v___x_378_; 
lean_dec_ref_known(v___x_376_, 1);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_361_, v___x_377_);
v_i_361_ = v___x_378_;
v_b_362_ = v___x_373_;
goto _start;
}
else
{
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0___boxed(lean_object* v_as_380_, lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_393_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_as_380_, v_sz_boxed_392_, v_i_boxed_393_, v_b_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_as_380_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(lean_object* v_letOrReassign_395_, lean_object* v_vars_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
if (lean_obj_tag(v_letOrReassign_395_) == 2)
{
lean_object* v___x_405_; size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v_sz_406_ = lean_array_size(v_vars_396_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo_spec__0(v_vars_396_, v_sz_406_, v___x_407_, v___x_405_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_408_, 0);
lean_dec(v_unused_416_);
v___x_410_ = v___x_408_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_dec(v___x_408_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_405_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_405_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
return v___x_408_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo___boxed(lean_object* v_letOrReassign_419_, lean_object* v_vars_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_419_, v_vars_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec_ref(v_vars_420_);
lean_dec(v_letOrReassign_419_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(lean_object* v___x_430_, lean_object* v_b_431_, uint8_t v_a_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Elab_Do_withErasedProj(v___x_430_, v_b_431_, v_a_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed(lean_object* v___x_442_, lean_object* v_b_443_, lean_object* v_a_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v_a_720__boxed_453_; lean_object* v_res_454_; 
v_a_720__boxed_453_ = lean_unbox(v_a_444_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0(v___x_442_, v_b_443_, v_a_720__boxed_453_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(uint8_t v_a_455_, lean_object* v_as_456_, size_t v_i_457_, size_t v_stop_458_, lean_object* v_b_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_eq(v_i_457_, v_stop_458_);
if (v___x_468_ == 0)
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; 
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_sub(v_i_457_, v___x_469_);
v___x_471_ = lean_array_uget_borrowed(v_as_456_, v___x_470_);
v___x_472_ = lean_box(v_a_455_);
lean_inc(v___x_471_);
v___f_473_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___lam__0___boxed), 11, 3);
lean_closure_set(v___f_473_, 0, v___x_471_);
lean_closure_set(v___f_473_, 1, v_b_459_);
lean_closure_set(v___f_473_, 2, v___x_472_);
v_i_457_ = v___x_470_;
v_b_459_ = v___f_473_;
goto _start;
}
else
{
lean_object* v___x_475_; 
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc_ref(v___y_460_);
v___x_475_ = lean_apply_8(v_b_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, lean_box(0));
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0___boxed(lean_object* v_a_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_stop_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_a_751__boxed_489_; size_t v_i_boxed_490_; size_t v_stop_boxed_491_; lean_object* v_res_492_; 
v_a_751__boxed_489_ = lean_unbox(v_a_476_);
v_i_boxed_490_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_stop_boxed_491_ = lean_unbox_usize(v_stop_479_);
lean_dec(v_stop_479_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v_a_751__boxed_489_, v_as_477_, v_i_boxed_490_, v_stop_boxed_491_, v_b_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v_as_477_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0(lean_object* v_letOrReassign_493_, lean_object* v_vars_494_, lean_object* v_k_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Elab_Do_LetOrReassign_registerReassignAliasInfo(v_letOrReassign_493_, v_vars_494_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_505_; 
lean_dec_ref_known(v___x_504_, 1);
v___x_505_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_493_, v_vars_494_, v___y_496_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_unbox(v_a_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_a_506_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v___y_496_);
v___x_508_ = lean_apply_8(v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_array_get_size(v_vars_494_);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_nat_dec_lt(v___x_510_, v___x_509_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec(v_a_506_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v___y_496_);
v___x_512_ = lean_apply_8(v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_512_;
}
else
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_usize_of_nat(v___x_509_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Do_elabWithReassignments_spec__0(v___x_515_, v_vars_494_, v___x_513_, v___x_514_, v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_516_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_k_495_);
v_a_517_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_505_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_505_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_k_495_);
v_a_525_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_504_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed(lean_object* v_letOrReassign_533_, lean_object* v_vars_534_, lean_object* v_k_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_Do_elabWithReassignments___lam__0(v_letOrReassign_533_, v_vars_534_, v_k_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v_vars_534_);
lean_dec(v_letOrReassign_533_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments(lean_object* v_letOrReassign_545_, lean_object* v_vars_546_, lean_object* v_k_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___f_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
lean_inc_ref(v_vars_546_);
lean_inc(v_letOrReassign_545_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___lam__0___boxed), 11, 3);
lean_closure_set(v___f_556_, 0, v_letOrReassign_545_);
lean_closure_set(v___f_556_, 1, v_vars_546_);
lean_closure_set(v___f_556_, 2, v_k_547_);
v___x_557_ = l_Lean_Elab_Do_LetOrReassign_getLetMutTk_x3f(v_letOrReassign_545_);
v___x_558_ = l_Lean_Elab_Do_LetOrReassign_isErasedDecl(v_letOrReassign_545_);
lean_dec(v_letOrReassign_545_);
v___x_559_ = l_Lean_Elab_Do_declareMutVars_x3f___redArg(v___x_557_, v_vars_546_, v___x_558_, v___f_556_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabWithReassignments___boxed(lean_object* v_letOrReassign_560_, lean_object* v_vars_561_, lean_object* v_k_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_560_, v_vars_561_, v_k_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec_ref(v_a_563_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(lean_object* v_a_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg___boxed(lean_object* v_a_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___redArg(v_a_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(lean_object* v_00_u03b1_590_, lean_object* v_a_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1___boxed(lean_object* v_00_u03b1_600_, lean_object* v_a_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__1(v_00_u03b1_600_, v_a_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_609_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box(1);
v___x_611_ = l_Lean_MessageData_ofFormat(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__2));
v___x_616_ = l_Lean_MessageData_ofFormat(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
return v_x_617_;
}
else
{
lean_object* v_head_619_; lean_object* v_tail_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_642_; 
v_head_619_ = lean_ctor_get(v_x_618_, 0);
v_tail_620_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_642_ == 0)
{
v___x_622_ = v_x_618_;
v_isShared_623_ = v_isSharedCheck_642_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_tail_620_);
lean_inc(v_head_619_);
lean_dec(v_x_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_642_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_before_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_640_; 
v_before_624_ = lean_ctor_get(v_head_619_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_head_619_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_head_619_, 1);
lean_dec(v_unused_641_);
v___x_626_ = v_head_619_;
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_before_624_);
lean_dec(v_head_619_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 7);
lean_ctor_set(v___x_626_, 1, v___x_628_);
lean_ctor_set(v___x_626_, 0, v_x_617_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_x_617_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_628_);
v___x_630_ = v_reuseFailAlloc_639_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__3);
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 7);
lean_ctor_set(v___x_622_, 1, v___x_631_);
lean_ctor_set(v___x_622_, 0, v___x_630_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = l_Lean_MessageData_ofSyntax(v_before_624_);
v___x_635_ = l_Lean_indentD(v___x_634_);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_633_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v_x_617_ = v___x_636_;
v_x_618_ = v_tail_620_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(lean_object* v_opts_643_, lean_object* v_opt_644_){
_start:
{
lean_object* v_name_645_; lean_object* v_defValue_646_; lean_object* v_map_647_; lean_object* v___x_648_; 
v_name_645_ = lean_ctor_get(v_opt_644_, 0);
v_defValue_646_ = lean_ctor_get(v_opt_644_, 1);
v_map_647_ = lean_ctor_get(v_opts_643_, 0);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_647_, v_name_645_);
if (lean_obj_tag(v___x_648_) == 0)
{
uint8_t v___x_649_; 
v___x_649_ = lean_unbox(v_defValue_646_);
return v___x_649_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_648_, 1);
if (lean_obj_tag(v_val_650_) == 1)
{
uint8_t v_v_651_; 
v_v_651_ = lean_ctor_get_uint8(v_val_650_, 0);
lean_dec_ref_known(v_val_650_, 0);
return v_v_651_;
}
else
{
uint8_t v___x_652_; 
lean_dec(v_val_650_);
v___x_652_ = lean_unbox(v_defValue_646_);
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_653_, lean_object* v_opt_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v_opts_653_, v_opt_654_);
lean_dec_ref(v_opt_654_);
lean_dec_ref(v_opts_653_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__1));
v___x_661_ = l_Lean_MessageData_ofFormat(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(lean_object* v_msgData_662_, lean_object* v_macroStack_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_toCold_666_; lean_object* v_options_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_toCold_666_ = lean_ctor_get(v___y_664_, 0);
v_options_667_ = lean_ctor_get(v_toCold_666_, 2);
v___x_668_ = l_Lean_Elab_pp_macroStack;
v___x_669_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__2(v_options_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_macroStack_663_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_msgData_662_);
return v___x_670_;
}
else
{
if (lean_obj_tag(v_macroStack_663_) == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v_msgData_662_);
return v___x_671_;
}
else
{
lean_object* v_head_672_; lean_object* v_after_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_688_; 
v_head_672_ = lean_ctor_get(v_macroStack_663_, 0);
lean_inc(v_head_672_);
v_after_673_ = lean_ctor_get(v_head_672_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_head_672_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_head_672_, 0);
lean_dec(v_unused_689_);
v___x_675_ = v_head_672_;
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_after_673_);
lean_dec(v_head_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3___closed__0);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 7);
lean_ctor_set(v___x_675_, 1, v___x_677_);
lean_ctor_set(v___x_675_, 0, v_msgData_662_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_msgData_662_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_687_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_msgData_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_680_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___closed__2);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_MessageData_ofSyntax(v_after_673_);
v___x_683_ = l_Lean_indentD(v___x_682_);
v_msgData_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_684_, 0, v___x_681_);
lean_ctor_set(v_msgData_684_, 1, v___x_683_);
v___x_685_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0_spec__3(v_msgData_684_, v_macroStack_663_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_690_, lean_object* v_macroStack_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_msgData_690_, v_macroStack_691_, v___y_692_);
lean_dec_ref(v___y_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(lean_object* v_msg_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_ref_703_; lean_object* v_macroStack_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_ref_703_ = lean_ctor_get(v___y_700_, 2);
v_macroStack_704_ = lean_ctor_get(v___y_696_, 1);
v___x_705_ = l_Lean_Elab_getBetterRef(v_ref_703_, v_macroStack_704_);
v___x_706_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_695_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
lean_inc(v_macroStack_704_);
v___x_708_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_a_707_, v_macroStack_704_, v___y_700_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_705_);
lean_ctor_set(v___x_713_, 1, v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg___boxed(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_726_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__5));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Array_mkArray0___redArg();
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_774_ = l_String_toRawSubstring_x27(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(lean_object* v_letOrReassign_821_, lean_object* v_decl_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
if (lean_obj_tag(v_letOrReassign_821_) == 2)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_822_);
v___x_831_ = l_Lean_Syntax_isOfKind(v_decl_822_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_833_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_834_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = l_Lean_Syntax_getArg(v_decl_822_, v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_837_);
v___x_839_ = l_Lean_Syntax_isOfKind(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___y_842_; lean_object* v_pattern_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; uint8_t v___x_913_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_837_);
v___x_913_ = l_Lean_Syntax_isOfKind(v___x_837_, v___x_840_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v___x_837_);
v___x_914_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_915_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_916_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = l_Lean_Syntax_getArg(v___x_837_, v___x_918_);
v___x_920_ = l_Lean_Syntax_matchesNull(v___x_919_, v___x_836_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v___x_837_);
v___x_921_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_922_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_923_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_924_;
}
else
{
lean_object* v_pattern_925_; lean_object* v_xType_x3f_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_pattern_925_ = l_Lean_Syntax_getArg(v___x_837_, v___x_836_);
v___x_961_ = lean_unsigned_to_nat(2u);
v___x_962_ = l_Lean_Syntax_getArg(v___x_837_, v___x_961_);
v___x_963_ = l_Lean_Syntax_isNone(v___x_962_);
if (v___x_963_ == 0)
{
uint8_t v___x_964_; 
lean_inc(v___x_962_);
v___x_964_ = l_Lean_Syntax_matchesNull(v___x_962_, v___x_918_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v___x_962_);
lean_dec(v_pattern_925_);
lean_dec(v___x_837_);
v___x_965_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_966_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_967_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = l_Lean_Syntax_getArg(v___x_962_, v___x_836_);
lean_dec(v___x_962_);
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_969_);
v___x_971_ = l_Lean_Syntax_isOfKind(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v___x_969_);
lean_dec(v_pattern_925_);
lean_dec(v___x_837_);
v___x_972_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_973_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_974_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_975_;
}
else
{
lean_object* v_xType_x3f_976_; lean_object* v___x_977_; 
lean_dec(v_decl_822_);
v_xType_x3f_976_ = l_Lean_Syntax_getArg(v___x_969_, v___x_918_);
lean_dec(v___x_969_);
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v_xType_x3f_976_);
v_xType_x3f_927_ = v___x_977_;
v___y_928_ = v_a_823_;
v___y_929_ = v_a_824_;
v___y_930_ = v_a_825_;
v___y_931_ = v_a_826_;
v___y_932_ = v_a_827_;
v___y_933_ = v_a_828_;
goto v___jp_926_;
}
}
}
else
{
lean_object* v___x_978_; 
lean_dec(v___x_962_);
lean_dec(v_decl_822_);
v___x_978_ = lean_box(0);
v_xType_x3f_927_ = v___x_978_;
v___y_928_ = v_a_823_;
v___y_929_ = v_a_824_;
v___y_930_ = v_a_825_;
v___y_931_ = v_a_826_;
v___y_932_ = v_a_827_;
v___y_933_ = v_a_828_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(4u);
v___x_935_ = l_Lean_Syntax_getArg(v___x_837_, v___x_934_);
lean_dec(v___x_837_);
if (lean_obj_tag(v_xType_x3f_927_) == 0)
{
v___y_842_ = v___x_935_;
v_pattern_843_ = v_pattern_925_;
v___y_844_ = v___y_928_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_930_;
v___y_847_ = v___y_931_;
v___y_848_ = v___y_932_;
v___y_849_ = v___y_933_;
goto v___jp_841_;
}
else
{
lean_object* v_toCold_936_; lean_object* v_val_937_; lean_object* v_ref_938_; lean_object* v_quotContext_939_; lean_object* v_currMacroScope_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_toCold_936_ = lean_ctor_get(v___y_932_, 0);
v_val_937_ = lean_ctor_get(v_xType_x3f_927_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_xType_x3f_927_, 1);
v_ref_938_ = lean_ctor_get(v___y_932_, 2);
v_quotContext_939_ = lean_ctor_get(v_toCold_936_, 8);
v_currMacroScope_940_ = lean_ctor_get(v_toCold_936_, 9);
v___x_941_ = l_Lean_SourceInfo_fromRef(v_ref_938_, v___x_839_);
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc_n(v___x_941_, 7);
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_941_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_947_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_948_ = lean_box(0);
lean_inc(v_currMacroScope_940_);
lean_inc(v_quotContext_939_);
v___x_949_ = l_Lean_addMacroScope(v_quotContext_939_, v___x_948_, v_currMacroScope_940_);
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_951_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_951_, 0, v___x_941_);
lean_ctor_set(v___x_951_, 1, v___x_947_);
lean_ctor_set(v___x_951_, 2, v___x_949_);
lean_ctor_set(v___x_951_, 3, v___x_950_);
v___x_952_ = l_Lean_Syntax_node1(v___x_941_, v___x_946_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node2(v___x_941_, v___x_943_, v___x_945_, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_941_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_957_ = l_Lean_Syntax_node1(v___x_941_, v___x_956_, v_val_937_);
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_941_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_Syntax_node5(v___x_941_, v___x_942_, v___x_953_, v_pattern_925_, v___x_955_, v___x_957_, v___x_959_);
v___y_842_ = v___x_935_;
v_pattern_843_ = v___x_960_;
v___y_844_ = v___y_928_;
v___y_845_ = v___y_929_;
v___y_846_ = v___y_930_;
v___y_847_ = v___y_931_;
v___y_848_ = v___y_932_;
v___y_849_ = v___y_933_;
goto v___jp_841_;
}
}
}
}
v___jp_841_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_850_ = lean_box(0);
v___x_851_ = lean_box(v___x_831_);
v___x_852_ = lean_box(v___x_831_);
lean_inc(v_pattern_843_);
v___x_853_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_853_, 0, v_pattern_843_);
lean_closure_set(v___x_853_, 1, v___x_850_);
lean_closure_set(v___x_853_, 2, v___x_851_);
lean_closure_set(v___x_853_, 3, v___x_852_);
v___x_854_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_853_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
v___x_856_ = lean_infer_type(v_a_855_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = l_Lean_Elab_Term_exprToSyntax(v_a_857_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_toCold_859_; lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_896_; 
v_toCold_859_ = lean_ctor_get(v___y_848_, 0);
v_a_860_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_896_ == 0)
{
v___x_862_ = v___x_858_;
v_isShared_863_ = v_isSharedCheck_896_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_896_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_ref_864_; lean_object* v_quotContext_865_; lean_object* v_currMacroScope_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_ref_864_ = lean_ctor_get(v___y_848_, 2);
v_quotContext_865_ = lean_ctor_get(v_toCold_859_, 8);
v_currMacroScope_866_ = lean_ctor_get(v_toCold_859_, 9);
v___x_867_ = l_Lean_SourceInfo_fromRef(v_ref_864_, v___x_839_);
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_869_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_867_, 11);
v___x_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_870_, 0, v___x_867_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
lean_ctor_set(v___x_870_, 2, v___x_869_);
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_867_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_875_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_867_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_878_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_879_ = lean_box(0);
lean_inc(v_currMacroScope_866_);
lean_inc(v_quotContext_865_);
v___x_880_ = l_Lean_addMacroScope(v_quotContext_865_, v___x_879_, v_currMacroScope_866_);
v___x_881_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__35));
v___x_882_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_882_, 0, v___x_867_);
lean_ctor_set(v___x_882_, 1, v___x_878_);
lean_ctor_set(v___x_882_, 2, v___x_880_);
lean_ctor_set(v___x_882_, 3, v___x_881_);
v___x_883_ = l_Lean_Syntax_node1(v___x_867_, v___x_877_, v___x_882_);
v___x_884_ = l_Lean_Syntax_node2(v___x_867_, v___x_874_, v___x_876_, v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_867_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_Syntax_node1(v___x_867_, v___x_868_, v_a_860_);
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_867_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_Syntax_node5(v___x_867_, v___x_873_, v___x_884_, v___y_842_, v___x_886_, v___x_887_, v___x_889_);
lean_inc_ref(v___x_870_);
v___x_891_ = l_Lean_Syntax_node5(v___x_867_, v___x_840_, v_pattern_843_, v___x_870_, v___x_870_, v___x_872_, v___x_890_);
v___x_892_ = l_Lean_Syntax_node1(v___x_867_, v___x_830_, v___x_891_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_892_);
v___x_894_ = v___x_862_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_dec(v_pattern_843_);
lean_dec(v___y_842_);
return v___x_858_;
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_pattern_843_);
lean_dec(v___y_842_);
v_a_897_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_856_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_856_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_pattern_843_);
lean_dec(v___y_842_);
v_a_905_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_854_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_854_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = l_Lean_Syntax_getArg(v___x_837_, v___x_836_);
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec(v___x_979_);
lean_dec(v___x_837_);
v___x_982_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_983_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_984_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_985_;
}
else
{
lean_object* v_x_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v_a_995_; lean_object* v_xType_x3f_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_x_986_ = l_Lean_Syntax_getArg(v___x_979_, v___x_836_);
lean_dec(v___x_979_);
v___x_1072_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_986_);
v___x_1073_ = l_Lean_Syntax_isOfKind(v_x_986_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_x_986_);
lean_dec(v___x_837_);
v___x_1074_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1075_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1076_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = l_Lean_Syntax_getArg(v___x_837_, v___x_1078_);
v___x_1080_ = l_Lean_Syntax_matchesNull(v___x_1079_, v___x_836_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_x_986_);
lean_dec(v___x_837_);
v___x_1081_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1082_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1083_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_unsigned_to_nat(2u);
v___x_1086_ = l_Lean_Syntax_getArg(v___x_837_, v___x_1085_);
v___x_1087_ = l_Lean_Syntax_isNone(v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; 
lean_inc(v___x_1086_);
v___x_1088_ = l_Lean_Syntax_matchesNull(v___x_1086_, v___x_1078_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v___x_1086_);
lean_dec(v_x_986_);
lean_dec(v___x_837_);
v___x_1089_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1090_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1091_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = l_Lean_Syntax_getArg(v___x_1086_, v___x_836_);
lean_dec(v___x_1086_);
v___x_1094_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_1093_);
v___x_1095_ = l_Lean_Syntax_isOfKind(v___x_1093_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v___x_1093_);
lean_dec(v_x_986_);
lean_dec(v___x_837_);
v___x_1096_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__6);
v___x_1097_ = l_Lean_MessageData_ofSyntax(v_decl_822_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v___x_1098_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_1099_;
}
else
{
lean_object* v_xType_x3f_1100_; lean_object* v___x_1101_; 
lean_dec(v_decl_822_);
v_xType_x3f_1100_ = l_Lean_Syntax_getArg(v___x_1093_, v___x_1078_);
lean_dec(v___x_1093_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_xType_x3f_1100_);
v_xType_x3f_1044_ = v___x_1101_;
v___y_1045_ = v_a_823_;
v___y_1046_ = v_a_824_;
v___y_1047_ = v_a_825_;
v___y_1048_ = v_a_826_;
v___y_1049_ = v_a_827_;
v___y_1050_ = v_a_828_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v___x_1102_; 
lean_dec(v___x_1086_);
lean_dec(v_decl_822_);
v___x_1102_ = lean_box(0);
v_xType_x3f_1044_ = v___x_1102_;
v___y_1045_ = v_a_823_;
v___y_1046_ = v_a_824_;
v___y_1047_ = v_a_825_;
v___y_1048_ = v_a_826_;
v___y_1049_ = v_a_827_;
v___y_1050_ = v_a_828_;
goto v___jp_1043_;
}
}
}
v___jp_987_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
lean_inc(v_x_986_);
v___x_997_ = l_Lean_Elab_Term_elabTermEnsuringType(v_x_986_, v_a_995_, v___x_831_, v___x_831_, v___x_996_, v___y_992_, v___y_991_, v___y_989_, v___y_988_, v___y_990_, v___y_994_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Lean_TSyntax_getId(v_x_986_);
v___x_999_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_998_, v___y_989_, v___y_988_, v___y_990_, v___y_994_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_LocalDecl_type(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1002_ = l_Lean_Elab_Term_exprToSyntax(v___x_1001_, v___y_992_, v___y_991_, v___y_989_, v___y_988_, v___y_990_, v___y_994_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1026_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_ref_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_ref_1007_ = lean_ctor_get(v___y_990_, 2);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1008_);
lean_inc_n(v___x_1009_, 7);
v___x_1010_ = l_Lean_Syntax_node1(v___x_1009_, v___x_980_, v_x_986_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1012_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1009_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1009_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_1009_, v___x_1014_, v___x_1016_, v_a_1003_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_1009_, v___x_1011_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1009_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node5(v___x_1009_, v___x_838_, v___x_1010_, v___x_1013_, v___x_1018_, v___x_1020_, v___y_993_);
v___x_1022_ = l_Lean_Syntax_node1(v___x_1009_, v___x_830_, v___x_1021_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1022_);
v___x_1024_ = v___x_1005_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_dec(v___y_993_);
lean_dec(v_x_986_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___y_993_);
lean_dec(v_x_986_);
v_a_1027_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_999_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_999_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___y_993_);
lean_dec(v_x_986_);
v_a_1035_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_997_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_997_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(4u);
v___x_1052_ = l_Lean_Syntax_getArg(v___x_837_, v___x_1051_);
lean_dec(v___x_837_);
if (lean_obj_tag(v_xType_x3f_1044_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_box(0);
v___y_988_ = v___y_1048_;
v___y_989_ = v___y_1047_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1046_;
v___y_992_ = v___y_1045_;
v___y_993_ = v___x_1052_;
v___y_994_ = v___y_1050_;
v_a_995_ = v___x_1053_;
goto v___jp_987_;
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1071_; 
v_val_1054_ = lean_ctor_get(v_xType_x3f_1044_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_xType_x3f_1044_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1056_ = v_xType_x3f_1044_;
v_isShared_1057_ = v_isSharedCheck_1071_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_val_1054_);
lean_dec(v_xType_x3f_1044_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1071_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Elab_Term_elabType(v_val_1054_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_a_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v___y_988_ = v___y_1048_;
v___y_989_ = v___y_1047_;
v___y_990_ = v___y_1049_;
v___y_991_ = v___y_1046_;
v___y_992_ = v___y_1045_;
v___y_993_ = v___x_1052_;
v___y_994_ = v___y_1050_;
v_a_995_ = v___x_1061_;
goto v___jp_987_;
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_1056_);
lean_dec(v___x_1052_);
lean_dec(v_x_986_);
v_a_1063_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1058_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1058_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
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
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_decl_822_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___boxed(lean_object* v_letOrReassign_1104_, lean_object* v_decl_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_1104_, v_decl_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_letOrReassign_1104_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(lean_object* v_00_u03b1_1114_, lean_object* v_msg_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___redArg(v_msg_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0(v_00_u03b1_1124_, v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(lean_object* v_msgData_1134_, lean_object* v_macroStack_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___redArg(v_msgData_1134_, v_macroStack_1135_, v___y_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0___boxed(lean_object* v_msgData_1144_, lean_object* v_macroStack_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment_spec__0_spec__0(v_msgData_1144_, v_macroStack_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1153_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__0));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__2));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(lean_object* v_config_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v_postponeValue_1166_; uint8_t v_generalize_1167_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; 
v_postponeValue_1166_ = lean_ctor_get_uint8(v_config_1160_, sizeof(void*)*1 + 3);
v_generalize_1167_ = lean_ctor_get_uint8(v_config_1160_, sizeof(void*)*1 + 4);
if (v_postponeValue_1166_ == 0)
{
v___y_1169_ = v_a_1161_;
v___y_1170_ = v_a_1162_;
v___y_1171_ = v_a_1163_;
v___y_1172_ = v_a_1164_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__3);
v___x_1178_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_1177_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1178_;
}
v___jp_1168_:
{
if (v_generalize_1167_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___closed__1);
v___x_1176_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_1175_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg___boxed(lean_object* v_config_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec_ref(v_config_1179_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(lean_object* v_config_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_1186_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___boxed(lean_object* v_config_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo(v_config_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_config_1196_);
return v_res_1205_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg(){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___closed__0);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg___boxed(lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0(lean_object* v_00_u03b1_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___boxed(lean_object* v_00_u03b1_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0(v_00_u03b1_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__2));
v___x_1242_ = l_String_toRawSubstring_x27(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__4));
v___x_1255_ = l_String_toRawSubstring_x27(v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(lean_object* v_decl_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_1278_);
v___x_1288_ = l_Lean_Syntax_isOfKind(v_decl_1278_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v_decl_1278_);
v___x_1289_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = l_Lean_Syntax_getArg(v_decl_1278_, v___x_1290_);
lean_dec(v_decl_1278_);
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_1291_);
v___x_1293_ = l_Lean_Syntax_isOfKind(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
lean_dec(v___x_1291_);
v___x_1294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = l_Lean_Syntax_getArg(v___x_1291_, v___x_1290_);
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_1295_);
v___x_1297_ = l_Lean_Syntax_isOfKind(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
lean_dec(v___x_1295_);
lean_dec(v___x_1291_);
v___x_1298_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v_t_x3f_1301_; lean_object* v___y_1302_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1299_ = l_Lean_Syntax_getArg(v___x_1295_, v___x_1290_);
lean_dec(v___x_1295_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_1299_);
v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1299_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec(v___x_1299_);
lean_dec(v___x_1291_);
v___x_1387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = l_Lean_Syntax_getArg(v___x_1291_, v___x_1388_);
v___x_1390_ = l_Lean_Syntax_matchesNull(v___x_1389_, v___x_1290_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
lean_dec(v___x_1299_);
lean_dec(v___x_1291_);
v___x_1391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1391_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(2u);
v___x_1393_ = l_Lean_Syntax_getArg(v___x_1291_, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_isNone(v___x_1393_);
if (v___x_1394_ == 0)
{
uint8_t v___x_1395_; 
lean_inc(v___x_1393_);
v___x_1395_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___x_1388_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec(v___x_1393_);
lean_dec(v___x_1299_);
lean_dec(v___x_1291_);
v___x_1396_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = l_Lean_Syntax_getArg(v___x_1393_, v___x_1290_);
lean_dec(v___x_1393_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_1397_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec(v___x_1397_);
lean_dec(v___x_1299_);
lean_dec(v___x_1291_);
v___x_1400_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_1400_;
}
else
{
lean_object* v_t_x3f_1401_; lean_object* v___x_1402_; 
v_t_x3f_1401_ = l_Lean_Syntax_getArg(v___x_1397_, v___x_1388_);
lean_dec(v___x_1397_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_t_x3f_1401_);
v_t_x3f_1301_ = v___x_1402_;
v___y_1302_ = v_a_1284_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v___x_1393_);
v___x_1403_ = lean_box(0);
v_t_x3f_1301_ = v___x_1403_;
v___y_1302_ = v_a_1284_;
goto v___jp_1300_;
}
}
}
v___jp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(4u);
v___x_1304_ = l_Lean_Syntax_getArg(v___x_1291_, v___x_1303_);
lean_dec(v___x_1291_);
if (lean_obj_tag(v_t_x3f_1301_) == 0)
{
lean_object* v_toCold_1305_; lean_object* v_ref_1306_; lean_object* v_quotContext_1307_; lean_object* v_currMacroScope_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_toCold_1305_ = lean_ctor_get(v___y_1302_, 0);
v_ref_1306_ = lean_ctor_get(v___y_1302_, 2);
v_quotContext_1307_ = lean_ctor_get(v_toCold_1305_, 8);
v_currMacroScope_1308_ = lean_ctor_get(v_toCold_1305_, 9);
v___x_1309_ = 0;
v___x_1310_ = l_Lean_SourceInfo_fromRef(v_ref_1306_, v___x_1309_);
lean_inc_n(v___x_1310_, 7);
v___x_1311_ = l_Lean_Syntax_node1(v___x_1310_, v___x_1296_, v___x_1299_);
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1313_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1310_);
lean_ctor_set(v___x_1314_, 1, v___x_1312_);
lean_ctor_set(v___x_1314_, 2, v___x_1313_);
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1310_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_1318_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3);
v___x_1319_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6));
lean_inc(v_currMacroScope_1308_);
lean_inc(v_quotContext_1307_);
v___x_1320_ = l_Lean_addMacroScope(v_quotContext_1307_, v___x_1319_, v_currMacroScope_1308_);
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8));
v___x_1322_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1310_);
lean_ctor_set(v___x_1322_, 1, v___x_1318_);
lean_ctor_set(v___x_1322_, 2, v___x_1320_);
lean_ctor_set(v___x_1322_, 3, v___x_1321_);
v___x_1323_ = l_Lean_Syntax_node1(v___x_1310_, v___x_1312_, v___x_1304_);
v___x_1324_ = l_Lean_Syntax_node2(v___x_1310_, v___x_1317_, v___x_1322_, v___x_1323_);
lean_inc_ref(v___x_1314_);
v___x_1325_ = l_Lean_Syntax_node5(v___x_1310_, v___x_1292_, v___x_1311_, v___x_1314_, v___x_1314_, v___x_1316_, v___x_1324_);
v___x_1326_ = l_Lean_Syntax_node1(v___x_1310_, v___x_1287_, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
else
{
lean_object* v_toCold_1328_; lean_object* v_val_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1384_; 
v_toCold_1328_ = lean_ctor_get(v___y_1302_, 0);
v_val_1329_ = lean_ctor_get(v_t_x3f_1301_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_t_x3f_1301_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1331_ = v_t_x3f_1301_;
v_isShared_1332_ = v_isSharedCheck_1384_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_val_1329_);
lean_dec(v_t_x3f_1301_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1384_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_ref_1333_; lean_object* v_quotContext_1334_; lean_object* v_currMacroScope_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v_ref_1333_ = lean_ctor_get(v___y_1302_, 2);
v_quotContext_1334_ = lean_ctor_get(v_toCold_1328_, 8);
v_currMacroScope_1335_ = lean_ctor_get(v_toCold_1328_, 9);
v___x_1336_ = 0;
v___x_1337_ = l_Lean_SourceInfo_fromRef(v_ref_1333_, v___x_1336_);
lean_inc_n(v___x_1337_, 19);
v___x_1338_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1296_, v___x_1299_);
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_1340_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_1341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1337_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
v___x_1342_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_1343_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_1344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1337_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_1346_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__9);
v___x_1347_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__10));
lean_inc_n(v_currMacroScope_1335_, 3);
lean_inc_n(v_quotContext_1334_, 3);
v___x_1348_ = l_Lean_addMacroScope(v_quotContext_1334_, v___x_1347_, v_currMacroScope_1335_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__14));
v___x_1350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1337_);
lean_ctor_set(v___x_1350_, 1, v___x_1346_);
lean_ctor_set(v___x_1350_, 2, v___x_1348_);
lean_ctor_set(v___x_1350_, 3, v___x_1349_);
v___x_1351_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1339_, v_val_1329_);
lean_inc(v___x_1351_);
v___x_1352_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1345_, v___x_1350_, v___x_1351_);
lean_inc_ref(v___x_1344_);
v___x_1353_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1342_, v___x_1344_, v___x_1352_);
v___x_1354_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1339_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_1356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1337_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__3);
v___x_1358_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__6));
v___x_1359_ = l_Lean_addMacroScope(v_quotContext_1334_, v___x_1358_, v_currMacroScope_1335_);
v___x_1360_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__8));
v___x_1361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1337_);
lean_ctor_set(v___x_1361_, 1, v___x_1357_);
lean_ctor_set(v___x_1361_, 2, v___x_1359_);
lean_ctor_set(v___x_1361_, 3, v___x_1360_);
v___x_1362_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__16));
v___x_1363_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__18));
v___x_1364_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_1365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1337_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_1367_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Lean_addMacroScope(v_quotContext_1334_, v___x_1368_, v_currMacroScope_1335_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__17));
v___x_1371_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1337_);
lean_ctor_set(v___x_1371_, 1, v___x_1367_);
lean_ctor_set(v___x_1371_, 2, v___x_1369_);
lean_ctor_set(v___x_1371_, 3, v___x_1370_);
v___x_1372_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1366_, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1363_, v___x_1365_, v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_1375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1337_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_Syntax_node5(v___x_1337_, v___x_1362_, v___x_1373_, v___x_1304_, v___x_1344_, v___x_1351_, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1339_, v___x_1376_);
v___x_1378_ = l_Lean_Syntax_node2(v___x_1337_, v___x_1345_, v___x_1361_, v___x_1377_);
v___x_1379_ = l_Lean_Syntax_node5(v___x_1337_, v___x_1292_, v___x_1338_, v___x_1341_, v___x_1354_, v___x_1356_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_node1(v___x_1337_, v___x_1287_, v___x_1379_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1380_);
v___x_1382_ = v___x_1331_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___boxed(lean_object* v_decl_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_decl_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(lean_object* v_lctx_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_keyedConfig_1423_; uint8_t v_trackZetaDelta_1424_; lean_object* v_zetaDeltaSet_1425_; lean_object* v_localInstances_1426_; lean_object* v_defEqCtx_x3f_1427_; lean_object* v_synthPendingDepth_1428_; lean_object* v_customCanUnfoldPredicate_x3f_1429_; uint8_t v_univApprox_1430_; uint8_t v_inTypeClassResolution_1431_; uint8_t v_cacheInferType_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_keyedConfig_1423_ = lean_ctor_get(v___y_1418_, 0);
v_trackZetaDelta_1424_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*7);
v_zetaDeltaSet_1425_ = lean_ctor_get(v___y_1418_, 1);
v_localInstances_1426_ = lean_ctor_get(v___y_1418_, 3);
v_defEqCtx_x3f_1427_ = lean_ctor_get(v___y_1418_, 4);
v_synthPendingDepth_1428_ = lean_ctor_get(v___y_1418_, 5);
v_customCanUnfoldPredicate_x3f_1429_ = lean_ctor_get(v___y_1418_, 6);
v_univApprox_1430_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1431_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*7 + 2);
v_cacheInferType_1432_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1429_);
lean_inc(v_synthPendingDepth_1428_);
lean_inc(v_defEqCtx_x3f_1427_);
lean_inc_ref(v_localInstances_1426_);
lean_inc(v_zetaDeltaSet_1425_);
lean_inc_ref(v_keyedConfig_1423_);
v___x_1433_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1433_, 0, v_keyedConfig_1423_);
lean_ctor_set(v___x_1433_, 1, v_zetaDeltaSet_1425_);
lean_ctor_set(v___x_1433_, 2, v_lctx_1414_);
lean_ctor_set(v___x_1433_, 3, v_localInstances_1426_);
lean_ctor_set(v___x_1433_, 4, v_defEqCtx_x3f_1427_);
lean_ctor_set(v___x_1433_, 5, v_synthPendingDepth_1428_);
lean_ctor_set(v___x_1433_, 6, v_customCanUnfoldPredicate_x3f_1429_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*7, v_trackZetaDelta_1424_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*7 + 1, v_univApprox_1430_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1431_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*7 + 3, v_cacheInferType_1432_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
v___x_1434_ = lean_apply_7(v_x_1415_, v___y_1416_, v___y_1417_, v___x_1433_, v___y_1419_, v___y_1420_, v___y_1421_, lean_box(0));
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
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
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg___boxed(lean_object* v_lctx_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v_lctx_1443_, v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(lean_object* v_00_u03b1_1453_, lean_object* v_lctx_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v_lctx_1454_, v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_lctx_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2(v_00_u03b1_1464_, v_lctx_1465_, v_x_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0(lean_object* v_k_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc_ref(v___y_1476_);
v___x_1485_ = lean_apply_9(v_k_1475_, v_b_1479_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0___boxed(lean_object* v_k_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0(v_k_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(lean_object* v_name_1497_, lean_object* v_type_1498_, lean_object* v_val_1499_, lean_object* v_k_1500_, uint8_t v_nondep_1501_, uint8_t v_kind_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___f_1511_; lean_object* v___x_1512_; 
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc_ref(v___y_1503_);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1511_, 0, v_k_1500_);
lean_closure_set(v___f_1511_, 1, v___y_1503_);
lean_closure_set(v___f_1511_, 2, v___y_1504_);
lean_closure_set(v___f_1511_, 3, v___y_1505_);
v___x_1512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1497_, v_type_1498_, v_val_1499_, v___f_1511_, v_nondep_1501_, v_kind_1502_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1512_) == 0)
{
return v___x_1512_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg___boxed(lean_object* v_name_1521_, lean_object* v_type_1522_, lean_object* v_val_1523_, lean_object* v_k_1524_, lean_object* v_nondep_1525_, lean_object* v_kind_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_nondep_boxed_1535_; uint8_t v_kind_boxed_1536_; lean_object* v_res_1537_; 
v_nondep_boxed_1535_ = lean_unbox(v_nondep_1525_);
v_kind_boxed_1536_ = lean_unbox(v_kind_1526_);
v_res_1537_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v_name_1521_, v_type_1522_, v_val_1523_, v_k_1524_, v_nondep_boxed_1535_, v_kind_boxed_1536_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(lean_object* v_00_u03b1_1538_, lean_object* v_name_1539_, lean_object* v_type_1540_, lean_object* v_val_1541_, lean_object* v_k_1542_, uint8_t v_nondep_1543_, uint8_t v_kind_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v_name_1539_, v_type_1540_, v_val_1541_, v_k_1542_, v_nondep_1543_, v_kind_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_name_1555_, lean_object* v_type_1556_, lean_object* v_val_1557_, lean_object* v_k_1558_, lean_object* v_nondep_1559_, lean_object* v_kind_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_nondep_boxed_1569_; uint8_t v_kind_boxed_1570_; lean_object* v_res_1571_; 
v_nondep_boxed_1569_ = lean_unbox(v_nondep_1559_);
v_kind_boxed_1570_ = lean_unbox(v_kind_1560_);
v_res_1571_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4(v_00_u03b1_1554_, v_name_1555_, v_type_1556_, v_val_1557_, v_k_1558_, v_nondep_boxed_1569_, v_kind_boxed_1570_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(lean_object* v_value_1572_, lean_object* v___x_1573_, uint8_t v___x_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, uint8_t v___x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Elab_Term_elabTermEnsuringType(v_value_1572_, v___x_1573_, v___x_1574_, v___x_1574_, v___x_1575_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = 1;
v___x_1588_ = l_Lean_Meta_mkLambdaFVars(v___x_1576_, v_a_1586_, v___x_1577_, v___x_1577_, v___x_1577_, v___x_1574_, v___x_1587_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1588_;
}
else
{
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed(lean_object* v_value_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_88119__boxed_1602_; uint8_t v___x_88122__boxed_1603_; lean_object* v_res_1604_; 
v___x_88119__boxed_1602_ = lean_unbox(v___x_1591_);
v___x_88122__boxed_1603_ = lean_unbox(v___x_1594_);
v_res_1604_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__0(v_value_1589_, v___x_1590_, v___x_88119__boxed_1602_, v___x_1592_, v___x_1593_, v___x_88122__boxed_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___x_1593_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(size_t v_sz_1605_, size_t v_i_1606_, lean_object* v_bs_1607_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1606_, v_sz_1605_);
if (v___x_1608_ == 0)
{
return v_bs_1607_;
}
else
{
lean_object* v_v_1609_; lean_object* v_snd_1610_; lean_object* v___x_1611_; lean_object* v_bs_x27_1612_; size_t v___x_1613_; size_t v___x_1614_; lean_object* v___x_1615_; 
v_v_1609_ = lean_array_uget_borrowed(v_bs_1607_, v_i_1606_);
v_snd_1610_ = lean_ctor_get(v_v_1609_, 1);
lean_inc(v_snd_1610_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v_bs_x27_1612_ = lean_array_uset(v_bs_1607_, v_i_1606_, v___x_1611_);
v___x_1613_ = ((size_t)1ULL);
v___x_1614_ = lean_usize_add(v_i_1606_, v___x_1613_);
v___x_1615_ = lean_array_uset(v_bs_x27_1612_, v_i_1606_, v_snd_1610_);
v_i_1606_ = v___x_1614_;
v_bs_1607_ = v___x_1615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1___boxed(lean_object* v_sz_1617_, lean_object* v_i_1618_, lean_object* v_bs_1619_){
_start:
{
size_t v_sz_boxed_1620_; size_t v_i_boxed_1621_; lean_object* v_res_1622_; 
v_sz_boxed_1620_ = lean_unbox_usize(v_sz_1617_);
lean_dec(v_sz_1617_);
v_i_boxed_1621_ = lean_unbox_usize(v_i_1618_);
lean_dec(v_i_1618_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_sz_boxed_1620_, v_i_boxed_1621_, v_bs_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v_ks_1627_; lean_object* v_vs_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1652_; 
v_ks_1627_ = lean_ctor_get(v_x_1623_, 0);
v_vs_1628_ = lean_ctor_get(v_x_1623_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1630_ = v_x_1623_;
v_isShared_1631_ = v_isSharedCheck_1652_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_vs_1628_);
lean_inc(v_ks_1627_);
lean_dec(v_x_1623_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1652_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = lean_array_get_size(v_ks_1627_);
v___x_1633_ = lean_nat_dec_lt(v_x_1624_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec(v_x_1624_);
v___x_1634_ = lean_array_push(v_ks_1627_, v_x_1625_);
v___x_1635_ = lean_array_push(v_vs_1628_, v_x_1626_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1635_);
lean_ctor_set(v___x_1630_, 0, v___x_1634_);
v___x_1637_ = v___x_1630_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
lean_object* v_k_x27_1639_; uint8_t v___x_1640_; 
v_k_x27_1639_ = lean_array_fget_borrowed(v_ks_1627_, v_x_1624_);
v___x_1640_ = l_Lean_instBEqFVarId_beq(v_x_1625_, v_k_x27_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1642_; 
if (v_isShared_1631_ == 0)
{
v___x_1642_ = v___x_1630_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_ks_1627_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_vs_1628_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_x_1624_, v___x_1643_);
lean_dec(v_x_1624_);
v_x_1623_ = v___x_1642_;
v_x_1624_ = v___x_1644_;
goto _start;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1647_ = lean_array_fset(v_ks_1627_, v_x_1624_, v_x_1625_);
v___x_1648_ = lean_array_fset(v_vs_1628_, v_x_1624_, v_x_1626_);
lean_dec(v_x_1624_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1648_);
lean_ctor_set(v___x_1630_, 0, v___x_1647_);
v___x_1650_ = v___x_1630_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(lean_object* v_n_1653_, lean_object* v_k_1654_, lean_object* v_v_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(v_n_1653_, v___x_1656_, v_k_1654_, v_v_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(lean_object* v_x_1659_, size_t v_x_1660_, size_t v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v_es_1664_; size_t v___x_1665_; size_t v___x_1666_; lean_object* v_j_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_es_1664_ = lean_ctor_get(v_x_1659_, 0);
v___x_1665_ = ((size_t)31ULL);
v___x_1666_ = lean_usize_land(v_x_1660_, v___x_1665_);
v_j_1667_ = lean_usize_to_nat(v___x_1666_);
v___x_1668_ = lean_array_get_size(v_es_1664_);
v___x_1669_ = lean_nat_dec_lt(v_j_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec(v_j_1667_);
lean_dec(v_x_1663_);
lean_dec(v_x_1662_);
return v_x_1659_;
}
else
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1708_; 
lean_inc_ref(v_es_1664_);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_x_1659_, 0);
lean_dec(v_unused_1709_);
v___x_1671_ = v_x_1659_;
v_isShared_1672_ = v_isSharedCheck_1708_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v_x_1659_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1708_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_v_1673_; lean_object* v___x_1674_; lean_object* v_xs_x27_1675_; lean_object* v___y_1677_; 
v_v_1673_ = lean_array_fget(v_es_1664_, v_j_1667_);
v___x_1674_ = lean_box(0);
v_xs_x27_1675_ = lean_array_fset(v_es_1664_, v_j_1667_, v___x_1674_);
switch(lean_obj_tag(v_v_1673_))
{
case 0:
{
lean_object* v_key_1682_; lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1693_; 
v_key_1682_ = lean_ctor_get(v_v_1673_, 0);
v_val_1683_ = lean_ctor_get(v_v_1673_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_v_1673_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1685_ = v_v_1673_;
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_inc(v_key_1682_);
lean_dec(v_v_1673_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_instBEqFVarId_beq(v_x_1662_, v_key_1682_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_del_object(v___x_1685_);
v___x_1688_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1682_, v_val_1683_, v_x_1662_, v_x_1663_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
v___y_1677_ = v___x_1689_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_val_1683_);
lean_dec(v_key_1682_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v_x_1663_);
lean_ctor_set(v___x_1685_, 0, v_x_1662_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_x_1662_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_x_1663_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v___y_1677_ = v___x_1691_;
goto v___jp_1676_;
}
}
}
}
case 1:
{
lean_object* v_node_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1706_; 
v_node_1694_ = lean_ctor_get(v_v_1673_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_v_1673_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1696_ = v_v_1673_;
v_isShared_1697_ = v_isSharedCheck_1706_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_node_1694_);
lean_dec(v_v_1673_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1706_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1698_ = ((size_t)5ULL);
v___x_1699_ = lean_usize_shift_right(v_x_1660_, v___x_1698_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_x_1661_, v___x_1700_);
v___x_1702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_node_1694_, v___x_1699_, v___x_1701_, v_x_1662_, v_x_1663_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1702_);
v___x_1704_ = v___x_1696_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v___y_1677_ = v___x_1704_;
goto v___jp_1676_;
}
}
}
default: 
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_x_1662_);
lean_ctor_set(v___x_1707_, 1, v_x_1663_);
v___y_1677_ = v___x_1707_;
goto v___jp_1676_;
}
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_array_fset(v_xs_x27_1675_, v_j_1667_, v___y_1677_);
lean_dec(v_j_1667_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1678_);
v___x_1680_ = v___x_1671_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
else
{
lean_object* v_ks_1710_; lean_object* v_vs_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1729_; 
v_ks_1710_ = lean_ctor_get(v_x_1659_, 0);
v_vs_1711_ = lean_ctor_get(v_x_1659_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_x_1659_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1713_ = v_x_1659_;
v_isShared_1714_ = v_isSharedCheck_1729_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_vs_1711_);
lean_inc(v_ks_1710_);
lean_dec(v_x_1659_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1729_;
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
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_ks_1710_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_vs_1711_);
v___x_1716_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v_newNode_1717_; size_t v___x_1718_; uint8_t v___x_1719_; 
v_newNode_1717_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v___x_1716_, v_x_1662_, v_x_1663_);
v___x_1718_ = ((size_t)7ULL);
v___x_1719_ = lean_usize_dec_le(v___x_1718_, v_x_1661_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1717_);
v___x_1721_ = lean_unsigned_to_nat(4u);
v___x_1722_ = lean_nat_dec_lt(v___x_1720_, v___x_1721_);
lean_dec(v___x_1720_);
if (v___x_1722_ == 0)
{
lean_object* v_ks_1723_; lean_object* v_vs_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_ks_1723_ = lean_ctor_get(v_newNode_1717_, 0);
lean_inc_ref(v_ks_1723_);
v_vs_1724_ = lean_ctor_get(v_newNode_1717_, 1);
lean_inc_ref(v_vs_1724_);
lean_dec_ref(v_newNode_1717_);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___closed__0);
v___x_1727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_x_1661_, v_ks_1723_, v_vs_1724_, v___x_1725_, v___x_1726_);
lean_dec_ref(v_vs_1724_);
lean_dec_ref(v_ks_1723_);
return v___x_1727_;
}
else
{
return v_newNode_1717_;
}
}
else
{
return v_newNode_1717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(size_t v_depth_1730_, lean_object* v_keys_1731_, lean_object* v_vals_1732_, lean_object* v_i_1733_, lean_object* v_entries_1734_){
_start:
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = lean_array_get_size(v_keys_1731_);
v___x_1736_ = lean_nat_dec_lt(v_i_1733_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_dec(v_i_1733_);
return v_entries_1734_;
}
else
{
lean_object* v_k_1737_; lean_object* v_v_1738_; uint64_t v___x_1739_; size_t v_h_1740_; size_t v___x_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; size_t v_h_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_k_1737_ = lean_array_fget_borrowed(v_keys_1731_, v_i_1733_);
v_v_1738_ = lean_array_fget_borrowed(v_vals_1732_, v_i_1733_);
v___x_1739_ = l_Lean_instHashableFVarId_hash(v_k_1737_);
v_h_1740_ = lean_uint64_to_usize(v___x_1739_);
v___x_1741_ = ((size_t)5ULL);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_sub(v_depth_1730_, v___x_1743_);
v___x_1745_ = lean_usize_mul(v___x_1741_, v___x_1744_);
v_h_1746_ = lean_usize_shift_right(v_h_1740_, v___x_1745_);
v___x_1747_ = lean_nat_add(v_i_1733_, v___x_1742_);
lean_dec(v_i_1733_);
lean_inc(v_v_1738_);
lean_inc(v_k_1737_);
v___x_1748_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_entries_1734_, v_h_1746_, v_depth_1730_, v_k_1737_, v_v_1738_);
v_i_1733_ = v___x_1747_;
v_entries_1734_ = v___x_1748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_depth_1750_, lean_object* v_keys_1751_, lean_object* v_vals_1752_, lean_object* v_i_1753_, lean_object* v_entries_1754_){
_start:
{
size_t v_depth_boxed_1755_; lean_object* v_res_1756_; 
v_depth_boxed_1755_ = lean_unbox_usize(v_depth_1750_);
lean_dec(v_depth_1750_);
v_res_1756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_boxed_1755_, v_keys_1751_, v_vals_1752_, v_i_1753_, v_entries_1754_);
lean_dec_ref(v_vals_1752_);
lean_dec_ref(v_keys_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
size_t v_x_88254__boxed_1762_; size_t v_x_88255__boxed_1763_; lean_object* v_res_1764_; 
v_x_88254__boxed_1762_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_x_88255__boxed_1763_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_res_1764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1757_, v_x_88254__boxed_1762_, v_x_88255__boxed_1763_, v_x_1760_, v_x_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
uint64_t v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = l_Lean_instHashableFVarId_hash(v_x_1766_);
v___x_1769_ = lean_uint64_to_usize(v___x_1768_);
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_1765_, v___x_1769_, v___x_1770_, v_x_1766_, v_x_1767_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(lean_object* v_as_1772_, size_t v_i_1773_, size_t v_stop_1774_, lean_object* v_b_1775_){
_start:
{
lean_object* v___y_1777_; uint8_t v___x_1781_; 
v___x_1781_ = lean_usize_dec_eq(v_i_1773_, v_stop_1774_);
if (v___x_1781_ == 0)
{
lean_object* v_fvarIdToDecl_1782_; lean_object* v_decls_1783_; lean_object* v_auxDeclToFullName_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_fvarIdToDecl_1782_ = lean_ctor_get(v_b_1775_, 0);
v_decls_1783_ = lean_ctor_get(v_b_1775_, 1);
v_auxDeclToFullName_1784_ = lean_ctor_get(v_b_1775_, 2);
v___x_1785_ = lean_array_uget_borrowed(v_as_1772_, v_i_1773_);
v___x_1786_ = l_Lean_Expr_fvarId_x21(v___x_1785_);
lean_inc_ref(v_b_1775_);
v___x_1787_ = lean_local_ctx_find(v_b_1775_, v___x_1786_);
if (lean_obj_tag(v___x_1787_) == 0)
{
v___y_1777_ = v_b_1775_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1814_; 
lean_inc(v_auxDeclToFullName_1784_);
lean_inc_ref(v_decls_1783_);
lean_inc_ref(v_fvarIdToDecl_1782_);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_b_1775_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; lean_object* v_unused_1816_; lean_object* v_unused_1817_; 
v_unused_1815_ = lean_ctor_get(v_b_1775_, 2);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_b_1775_, 1);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_b_1775_, 0);
lean_dec(v_unused_1817_);
v___x_1789_ = v_b_1775_;
v_isShared_1790_ = v_isSharedCheck_1814_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v_b_1775_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1814_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_val_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1813_; 
v_val_1791_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1793_ = v___x_1787_;
v_isShared_1794_ = v_isSharedCheck_1813_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_val_1791_);
lean_dec(v___x_1787_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1813_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1809_; lean_object* v_fvarId_1812_; 
v___x_1795_ = l_Lean_LocalDecl_type(v_val_1791_);
v___x_1796_ = l_Lean_Expr_cleanupAnnotations(v___x_1795_);
v___x_1797_ = l_Lean_LocalDecl_setType(v_val_1791_, v___x_1796_);
v_fvarId_1812_ = lean_ctor_get(v___x_1797_, 1);
lean_inc(v_fvarId_1812_);
v___y_1809_ = v_fvarId_1812_;
goto v___jp_1808_;
v___jp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1797_);
v___x_1802_ = v___x_1793_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1797_);
v___x_1802_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = l_Lean_PersistentArray_set___redArg(v_decls_1783_, v___y_1800_, v___x_1802_);
lean_dec(v___y_1800_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1803_);
lean_ctor_set(v___x_1789_, 0, v___y_1799_);
v___x_1805_ = v___x_1789_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___y_1799_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_auxDeclToFullName_1784_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
v___y_1777_ = v___x_1805_;
goto v___jp_1776_;
}
}
}
v___jp_1808_:
{
lean_object* v___x_1810_; lean_object* v_index_1811_; 
lean_inc_ref(v___x_1797_);
v___x_1810_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_fvarIdToDecl_1782_, v___y_1809_, v___x_1797_);
v_index_1811_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_index_1811_);
v___y_1799_ = v___x_1810_;
v___y_1800_ = v_index_1811_;
goto v___jp_1798_;
}
}
}
}
}
else
{
return v_b_1775_;
}
v___jp_1776_:
{
size_t v___x_1778_; size_t v___x_1779_; 
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1773_, v___x_1778_);
v_i_1773_ = v___x_1779_;
v_b_1775_ = v___y_1777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3___boxed(lean_object* v_as_1818_, lean_object* v_i_1819_, lean_object* v_stop_1820_, lean_object* v_b_1821_){
_start:
{
size_t v_i_boxed_1822_; size_t v_stop_boxed_1823_; lean_object* v_res_1824_; 
v_i_boxed_1822_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_stop_boxed_1823_ = lean_unbox_usize(v_stop_1820_);
lean_dec(v_stop_1820_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v_as_1818_, v_i_boxed_1822_, v_stop_boxed_1823_, v_b_1821_);
lean_dec_ref(v_as_1818_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__0));
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__2));
v___x_1830_ = l_Lean_stringToMessageData(v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__4));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(lean_object* v_type_1836_, lean_object* v_value_1837_, uint8_t v___x_1838_, uint8_t v___x_1839_, lean_object* v___x_1840_, uint8_t v___y_1841_, lean_object* v_xs_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
size_t v_sz_1850_; size_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; 
v_sz_1850_ = lean_array_size(v_xs_1842_);
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__1(v_sz_1850_, v___x_1851_, v_xs_1842_);
lean_inc(v_type_1836_);
v___x_1853_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType___boxed), 8, 1);
lean_closure_set(v___x_1853_, 0, v_type_1836_);
v___x_1854_ = 2;
v___x_1855_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1853_, v___x_1854_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___y_1858_; lean_object* v___y_1894_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
if (v___y_1841_ == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
v___y_1894_ = v___x_1930_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1931_; 
v___x_1931_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__7));
v___y_1894_ = v___x_1931_;
goto v___jp_1893_;
}
v___jp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; 
lean_inc(v_a_1856_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1856_);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_box(v___x_1838_);
v___x_1862_ = lean_box(v___x_1839_);
lean_inc_ref(v___x_1852_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1863_, 0, v_value_1837_);
lean_closure_set(v___f_1863_, 1, v___x_1859_);
lean_closure_set(v___f_1863_, 2, v___x_1861_);
lean_closure_set(v___f_1863_, 3, v___x_1860_);
lean_closure_set(v___f_1863_, 4, v___x_1852_);
lean_closure_set(v___f_1863_, 5, v___x_1862_);
v___x_1864_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__2___redArg(v___y_1858_, v___f_1863_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = 1;
v___x_1867_ = l_Lean_Meta_mkForallFVars(v___x_1852_, v_a_1856_, v___x_1839_, v___x_1838_, v___x_1838_, v___x_1866_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec_ref(v___x_1852_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1868_);
lean_ctor_set(v___x_1872_, 1, v_a_1865_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_a_1865_);
v_a_1877_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1867_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1867_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1852_);
v_a_1885_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1864_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1864_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
v___jp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1895_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__1);
lean_inc_ref(v___y_1894_);
v___x_1896_ = l_Lean_stringToMessageData(v___y_1894_);
lean_inc_ref(v___x_1896_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__3);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
lean_inc(v_type_1836_);
v___x_1900_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_1856_, v_type_1836_, v___x_1899_, v___y_1844_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1901_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__5);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1896_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1898_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_inc(v_a_1856_);
v___x_1905_ = l_Lean_Elab_Term_registerLevelMVarErrorExprInfo___redArg(v_a_1856_, v_type_1836_, v___x_1904_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_lctx_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
lean_dec_ref_known(v___x_1905_, 1);
v_lctx_1906_ = lean_ctor_get(v___y_1845_, 2);
v___x_1907_ = lean_array_get_size(v___x_1852_);
v___x_1908_ = lean_nat_dec_lt(v___x_1840_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_inc_ref(v_lctx_1906_);
v___y_1858_ = v_lctx_1906_;
goto v___jp_1857_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_le(v___x_1907_, v___x_1907_);
if (v___x_1909_ == 0)
{
if (v___x_1908_ == 0)
{
lean_inc_ref(v_lctx_1906_);
v___y_1858_ = v_lctx_1906_;
goto v___jp_1857_;
}
else
{
size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_usize_of_nat(v___x_1907_);
lean_inc_ref(v_lctx_1906_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v___x_1852_, v___x_1851_, v___x_1910_, v_lctx_1906_);
v___y_1858_ = v___x_1911_;
goto v___jp_1857_;
}
}
else
{
size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_usize_of_nat(v___x_1907_);
lean_inc_ref(v_lctx_1906_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__3(v___x_1852_, v___x_1851_, v___x_1912_, v_lctx_1906_);
v___y_1858_ = v___x_1913_;
goto v___jp_1857_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1905_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1905_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v___x_1896_);
lean_dec(v_a_1856_);
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
lean_dec(v_type_1836_);
v_a_1922_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1900_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1900_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___x_1852_);
lean_dec(v_value_1837_);
lean_dec(v_type_1836_);
v_a_1932_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1855_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1855_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed(lean_object* v_type_1940_, lean_object* v_value_1941_, lean_object* v___x_1942_, lean_object* v___x_1943_, lean_object* v___x_1944_, lean_object* v___y_1945_, lean_object* v_xs_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v___x_88551__boxed_1954_; uint8_t v___x_88552__boxed_1955_; uint8_t v___y_88554__boxed_1956_; lean_object* v_res_1957_; 
v___x_88551__boxed_1954_ = lean_unbox(v___x_1942_);
v___x_88552__boxed_1955_ = lean_unbox(v___x_1943_);
v___y_88554__boxed_1956_ = lean_unbox(v___y_1945_);
v_res_1957_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__1(v_type_1940_, v_value_1941_, v___x_88551__boxed_1954_, v___x_88552__boxed_1955_, v___x_1944_, v___y_88554__boxed_1956_, v_xs_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___x_1944_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(lean_object* v_val_1958_, lean_object* v_a_1959_, lean_object* v_letOrReassign_1960_, lean_object* v_a_1961_, uint8_t v_zeta_1962_, uint8_t v___y_1963_, lean_object* v_x_1964_, uint8_t v_usedOnly_1965_, uint8_t v___x_1966_, lean_object* v_snd_1967_, lean_object* v_h_x27_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
lean_inc_ref(v_h_x27_1968_);
v___x_1977_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_1958_, v_h_x27_1968_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref_known(v___x_1977_, 1);
v___x_1978_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_1978_, 0, v_a_1959_);
v___x_1979_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_1960_, v_a_1961_, v___x_1978_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1979_) == 0)
{
if (v_zeta_1962_ == 0)
{
if (v___y_1963_ == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_snd_1967_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = lean_unsigned_to_nat(2u);
v___x_1982_ = lean_mk_empty_array_with_capacity(v___x_1981_);
v___x_1983_ = lean_array_push(v___x_1982_, v_x_1964_);
v___x_1984_ = lean_array_push(v___x_1983_, v_h_x27_1968_);
v___x_1985_ = 1;
v___x_1986_ = l_Lean_Meta_mkLetFVars(v___x_1984_, v_a_1980_, v_usedOnly_1965_, v___y_1963_, v___x_1985_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec_ref(v___x_1984_);
return v___x_1986_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v_a_1987_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1988_ = lean_unsigned_to_nat(2u);
v___x_1989_ = lean_mk_empty_array_with_capacity(v___x_1988_);
v___x_1990_ = lean_array_push(v___x_1989_, v_x_1964_);
v___x_1991_ = lean_array_push(v___x_1990_, v_h_x27_1968_);
v___x_1992_ = 1;
v___x_1993_ = l_Lean_Meta_mkLambdaFVars(v___x_1991_, v_a_1987_, v_zeta_1962_, v___x_1966_, v_zeta_1962_, v___x_1966_, v___x_1992_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec_ref(v___x_1991_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
lean_inc_ref(v_snd_1967_);
v___x_1995_ = l_Lean_Meta_mkEqRefl(v_snd_1967_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = l_Lean_mkAppB(v_a_1994_, v_snd_1967_, v_a_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_dec(v_a_1994_);
lean_dec_ref(v_snd_1967_);
return v___x_1995_;
}
}
else
{
lean_dec_ref(v_snd_1967_);
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2005_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_2006_ = lean_unsigned_to_nat(2u);
v___x_2007_ = lean_mk_empty_array_with_capacity(v___x_2006_);
lean_inc_ref(v___x_2007_);
v___x_2008_ = lean_array_push(v___x_2007_, v_x_1964_);
v___x_2009_ = lean_array_push(v___x_2008_, v_h_x27_1968_);
v___x_2010_ = l_Lean_Expr_abstractM(v_a_2005_, v___x_2009_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc_ref(v_snd_1967_);
v___x_2012_ = l_Lean_Meta_mkEqRefl(v_snd_1967_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2023_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2017_ = lean_array_push(v___x_2007_, v_snd_1967_);
v___x_2018_ = lean_array_push(v___x_2017_, v_a_2013_);
v___x_2019_ = lean_expr_instantiate_rev(v_a_2011_, v___x_2018_);
lean_dec_ref(v___x_2018_);
lean_dec(v_a_2011_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_dec(v_a_2011_);
lean_dec_ref(v___x_2007_);
lean_dec_ref(v_snd_1967_);
return v___x_2012_;
}
}
else
{
lean_dec_ref(v___x_2007_);
lean_dec_ref(v_snd_1967_);
return v___x_2010_;
}
}
}
else
{
lean_dec_ref(v_h_x27_1968_);
lean_dec_ref(v_snd_1967_);
lean_dec_ref(v_x_1964_);
return v___x_1979_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_h_x27_1968_);
lean_dec_ref(v_snd_1967_);
lean_dec_ref(v_x_1964_);
lean_dec_ref(v_a_1961_);
lean_dec(v_letOrReassign_1960_);
lean_dec_ref(v_a_1959_);
v_a_2024_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1977_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1977_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed(lean_object** _args){
lean_object* v_val_2032_ = _args[0];
lean_object* v_a_2033_ = _args[1];
lean_object* v_letOrReassign_2034_ = _args[2];
lean_object* v_a_2035_ = _args[3];
lean_object* v_zeta_2036_ = _args[4];
lean_object* v___y_2037_ = _args[5];
lean_object* v_x_2038_ = _args[6];
lean_object* v_usedOnly_2039_ = _args[7];
lean_object* v___x_2040_ = _args[8];
lean_object* v_snd_2041_ = _args[9];
lean_object* v_h_x27_2042_ = _args[10];
lean_object* v___y_2043_ = _args[11];
lean_object* v___y_2044_ = _args[12];
lean_object* v___y_2045_ = _args[13];
lean_object* v___y_2046_ = _args[14];
lean_object* v___y_2047_ = _args[15];
lean_object* v___y_2048_ = _args[16];
lean_object* v___y_2049_ = _args[17];
lean_object* v___y_2050_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2051_; uint8_t v___y_88779__boxed_2052_; uint8_t v_usedOnly_boxed_2053_; uint8_t v___x_88780__boxed_2054_; lean_object* v_res_2055_; 
v_zeta_boxed_2051_ = lean_unbox(v_zeta_2036_);
v___y_88779__boxed_2052_ = lean_unbox(v___y_2037_);
v_usedOnly_boxed_2053_ = lean_unbox(v_usedOnly_2039_);
v___x_88780__boxed_2054_ = lean_unbox(v___x_2040_);
v_res_2055_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__2(v_val_2032_, v_a_2033_, v_letOrReassign_2034_, v_a_2035_, v_zeta_boxed_2051_, v___y_88779__boxed_2052_, v_x_2038_, v_usedOnly_boxed_2053_, v___x_88780__boxed_2054_, v_snd_2041_, v_h_x27_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(lean_object* v_id_2056_, lean_object* v_eq_x3f_2057_, lean_object* v_a_2058_, lean_object* v_letOrReassign_2059_, lean_object* v_a_2060_, uint8_t v_zeta_2061_, uint8_t v_usedOnly_2062_, lean_object* v_snd_2063_, uint8_t v___y_2064_, uint8_t v___x_2065_, lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
lean_inc_ref(v_x_2066_);
v___x_2075_ = l_Lean_Elab_Term_addLocalVarInfo(v_id_2056_, v_x_2066_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref_known(v___x_2075_, 1);
if (lean_obj_tag(v_eq_x3f_2057_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_2076_, 0, v_a_2058_);
v___x_2077_ = l_Lean_Elab_Do_elabWithReassignments(v_letOrReassign_2059_, v_a_2060_, v___x_2076_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2077_) == 0)
{
if (v_zeta_2061_ == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v_snd_2063_);
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_mk_empty_array_with_capacity(v___x_2079_);
v___x_2081_ = lean_array_push(v___x_2080_, v_x_2066_);
v___x_2082_ = 1;
v___x_2083_ = l_Lean_Meta_mkLetFVars(v___x_2081_, v_a_2078_, v_usedOnly_2062_, v_zeta_2061_, v___x_2082_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec_ref(v___x_2081_);
return v___x_2083_;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2084_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_mk_empty_array_with_capacity(v___x_2085_);
v___x_2087_ = lean_array_push(v___x_2086_, v_x_2066_);
v___x_2088_ = l_Lean_Expr_abstractM(v_a_2084_, v___x_2087_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec_ref(v___x_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_expr_instantiate1(v_a_2089_, v_snd_2063_);
lean_dec_ref(v_snd_2063_);
lean_dec(v_a_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_dec_ref(v_snd_2063_);
return v___x_2088_;
}
}
}
else
{
lean_dec_ref(v_x_2066_);
lean_dec_ref(v_snd_2063_);
return v___x_2077_;
}
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; 
v_val_2098_ = lean_ctor_get(v_eq_x3f_2057_, 0);
lean_inc_n(v_val_2098_, 2);
lean_dec_ref_known(v_eq_x3f_2057_, 1);
v___x_2099_ = lean_box(v_zeta_2061_);
v___x_2100_ = lean_box(v___y_2064_);
v___x_2101_ = lean_box(v_usedOnly_2062_);
v___x_2102_ = lean_box(v___x_2065_);
lean_inc_ref(v_snd_2063_);
lean_inc_ref_n(v_x_2066_, 2);
v___f_2103_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__2___boxed), 19, 10);
lean_closure_set(v___f_2103_, 0, v_val_2098_);
lean_closure_set(v___f_2103_, 1, v_a_2058_);
lean_closure_set(v___f_2103_, 2, v_letOrReassign_2059_);
lean_closure_set(v___f_2103_, 3, v_a_2060_);
lean_closure_set(v___f_2103_, 4, v___x_2099_);
lean_closure_set(v___f_2103_, 5, v___x_2100_);
lean_closure_set(v___f_2103_, 6, v_x_2066_);
lean_closure_set(v___f_2103_, 7, v___x_2101_);
lean_closure_set(v___f_2103_, 8, v___x_2102_);
lean_closure_set(v___f_2103_, 9, v_snd_2063_);
v___x_2104_ = l_Lean_Meta_mkEq(v_x_2066_, v_snd_2063_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Meta_mkEqRefl(v_x_2066_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_TSyntax_getId(v_val_2098_);
lean_dec(v_val_2098_);
v___x_2109_ = 0;
v___x_2110_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_2108_, v_a_2105_, v_a_2107_, v___f_2103_, v___x_2065_, v___x_2109_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2110_;
}
else
{
lean_dec(v_a_2105_);
lean_dec_ref(v___f_2103_);
lean_dec(v_val_2098_);
return v___x_2106_;
}
}
else
{
lean_dec_ref(v___f_2103_);
lean_dec(v_val_2098_);
lean_dec_ref(v_x_2066_);
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_x_2066_);
lean_dec_ref(v_snd_2063_);
lean_dec_ref(v_a_2060_);
lean_dec(v_letOrReassign_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_eq_x3f_2057_);
v_a_2111_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2075_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2075_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed(lean_object** _args){
lean_object* v_id_2119_ = _args[0];
lean_object* v_eq_x3f_2120_ = _args[1];
lean_object* v_a_2121_ = _args[2];
lean_object* v_letOrReassign_2122_ = _args[3];
lean_object* v_a_2123_ = _args[4];
lean_object* v_zeta_2124_ = _args[5];
lean_object* v_usedOnly_2125_ = _args[6];
lean_object* v_snd_2126_ = _args[7];
lean_object* v___y_2127_ = _args[8];
lean_object* v___x_2128_ = _args[9];
lean_object* v_x_2129_ = _args[10];
lean_object* v___y_2130_ = _args[11];
lean_object* v___y_2131_ = _args[12];
lean_object* v___y_2132_ = _args[13];
lean_object* v___y_2133_ = _args[14];
lean_object* v___y_2134_ = _args[15];
lean_object* v___y_2135_ = _args[16];
lean_object* v___y_2136_ = _args[17];
lean_object* v___y_2137_ = _args[18];
_start:
{
uint8_t v_zeta_boxed_2138_; uint8_t v_usedOnly_boxed_2139_; uint8_t v___y_88937__boxed_2140_; uint8_t v___x_88938__boxed_2141_; lean_object* v_res_2142_; 
v_zeta_boxed_2138_ = lean_unbox(v_zeta_2124_);
v_usedOnly_boxed_2139_ = lean_unbox(v_usedOnly_2125_);
v___y_88937__boxed_2140_ = lean_unbox(v___y_2127_);
v___x_88938__boxed_2141_ = lean_unbox(v___x_2128_);
v_res_2142_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__3(v_id_2119_, v_eq_x3f_2120_, v_a_2121_, v_letOrReassign_2122_, v_a_2123_, v_zeta_boxed_2138_, v_usedOnly_boxed_2139_, v_snd_2126_, v___y_88937__boxed_2140_, v___x_88938__boxed_2141_, v_x_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(uint8_t v___x_2143_, lean_object* v_____do__lift_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2144_, v___x_2143_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed(lean_object* v___x_2155_, lean_object* v_____do__lift_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_89065__boxed_2165_; lean_object* v_res_2166_; 
v___x_89065__boxed_2165_ = lean_unbox(v___x_2155_);
v_res_2166_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__4(v___x_89065__boxed_2165_, v_____do__lift_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v_____do__lift_2156_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(lean_object* v_term_2167_, lean_object* v___x_2168_, uint8_t v___x_2169_, lean_object* v___x_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Elab_Term_elabTermEnsuringType(v_term_2167_, v___x_2168_, v___x_2169_, v___x_2169_, v___x_2170_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed(lean_object* v_term_2180_, lean_object* v___x_2181_, lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v___x_89100__boxed_2192_; lean_object* v_res_2193_; 
v___x_89100__boxed_2192_ = lean_unbox(v___x_2182_);
v_res_2193_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__5(v_term_2180_, v___x_2181_, v___x_89100__boxed_2192_, v___x_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0(lean_object* v_stx_2194_, lean_object* v_output_2195_, lean_object* v_trees_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_lctx_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_lctx_2204_ = lean_ctor_get(v___y_2199_, 2);
lean_inc_ref(v_lctx_2204_);
v___x_2205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2205_, 0, v_lctx_2204_);
lean_ctor_set(v___x_2205_, 1, v_stx_2194_);
lean_ctor_set(v___x_2205_, 2, v_output_2195_);
v___x_2206_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_trees_2196_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_stx_2209_, lean_object* v_output_2210_, lean_object* v_trees_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0(v_stx_2209_, v_output_2210_, v_trees_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2219_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = lean_unsigned_to_nat(32u);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1(void){
_start:
{
size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2223_ = ((size_t)5ULL);
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = lean_unsigned_to_nat(32u);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
v___x_2227_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__0);
v___x_2228_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
lean_ctor_set(v___x_2228_, 2, v___x_2224_);
lean_ctor_set(v___x_2228_, 3, v___x_2224_);
lean_ctor_set_usize(v___x_2228_, 4, v___x_2223_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v_infoState_2232_; lean_object* v_trees_2233_; lean_object* v___x_2234_; lean_object* v_infoState_2235_; lean_object* v_env_2236_; lean_object* v_nextMacroScope_2237_; lean_object* v_ngen_2238_; lean_object* v_auxDeclNGen_2239_; lean_object* v_traceState_2240_; lean_object* v_cache_2241_; lean_object* v_messages_2242_; lean_object* v_snapshotTasks_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2264_; 
v___x_2231_ = lean_st_ref_get(v___y_2229_);
v_infoState_2232_ = lean_ctor_get(v___x_2231_, 7);
lean_inc_ref(v_infoState_2232_);
lean_dec(v___x_2231_);
v_trees_2233_ = lean_ctor_get(v_infoState_2232_, 2);
lean_inc_ref(v_trees_2233_);
lean_dec_ref(v_infoState_2232_);
v___x_2234_ = lean_st_ref_take(v___y_2229_);
v_infoState_2235_ = lean_ctor_get(v___x_2234_, 7);
v_env_2236_ = lean_ctor_get(v___x_2234_, 0);
v_nextMacroScope_2237_ = lean_ctor_get(v___x_2234_, 1);
v_ngen_2238_ = lean_ctor_get(v___x_2234_, 2);
v_auxDeclNGen_2239_ = lean_ctor_get(v___x_2234_, 3);
v_traceState_2240_ = lean_ctor_get(v___x_2234_, 4);
v_cache_2241_ = lean_ctor_get(v___x_2234_, 5);
v_messages_2242_ = lean_ctor_get(v___x_2234_, 6);
v_snapshotTasks_2243_ = lean_ctor_get(v___x_2234_, 8);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2245_ = v___x_2234_;
v_isShared_2246_ = v_isSharedCheck_2264_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snapshotTasks_2243_);
lean_inc(v_infoState_2235_);
lean_inc(v_messages_2242_);
lean_inc(v_cache_2241_);
lean_inc(v_traceState_2240_);
lean_inc(v_auxDeclNGen_2239_);
lean_inc(v_ngen_2238_);
lean_inc(v_nextMacroScope_2237_);
lean_inc(v_env_2236_);
lean_dec(v___x_2234_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2264_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v_enabled_2247_; lean_object* v_assignment_2248_; lean_object* v_lazyAssignment_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2262_; 
v_enabled_2247_ = lean_ctor_get_uint8(v_infoState_2235_, sizeof(void*)*3);
v_assignment_2248_ = lean_ctor_get(v_infoState_2235_, 0);
v_lazyAssignment_2249_ = lean_ctor_get(v_infoState_2235_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_infoState_2235_);
if (v_isSharedCheck_2262_ == 0)
{
lean_object* v_unused_2263_; 
v_unused_2263_ = lean_ctor_get(v_infoState_2235_, 2);
lean_dec(v_unused_2263_);
v___x_2251_ = v_infoState_2235_;
v_isShared_2252_ = v_isSharedCheck_2262_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_lazyAssignment_2249_);
lean_inc(v_assignment_2248_);
lean_dec(v_infoState_2235_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2262_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___closed__1);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 2, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_assignment_2248_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_lazyAssignment_2249_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v___x_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, sizeof(void*)*3, v_enabled_2247_);
v___x_2255_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 7, v___x_2255_);
v___x_2257_ = v___x_2245_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_env_2236_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_nextMacroScope_2237_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_ngen_2238_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_auxDeclNGen_2239_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_traceState_2240_);
lean_ctor_set(v_reuseFailAlloc_2260_, 5, v_cache_2241_);
lean_ctor_set(v_reuseFailAlloc_2260_, 6, v_messages_2242_);
lean_ctor_set(v_reuseFailAlloc_2260_, 7, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2260_, 8, v_snapshotTasks_2243_);
v___x_2257_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_st_ref_put(v___y_2229_, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_trees_2233_);
return v___x_2259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg___boxed(lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2265_);
lean_dec(v___y_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(lean_object* v___y_2268_, lean_object* v_mkInfoTree_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v_a_2275_, lean_object* v_a_x3f_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v_infoState_2279_; lean_object* v_trees_2280_; lean_object* v___x_2281_; 
v___x_2278_ = lean_st_ref_get(v___y_2268_);
v_infoState_2279_ = lean_ctor_get(v___x_2278_, 7);
lean_inc_ref(v_infoState_2279_);
lean_dec(v___x_2278_);
v_trees_2280_ = lean_ctor_get(v_infoState_2279_, 2);
lean_inc_ref(v_trees_2280_);
lean_dec_ref(v_infoState_2279_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
v___x_2281_ = lean_apply_8(v_mkInfoTree_2269_, v_trees_2280_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2268_, lean_box(0));
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2320_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2320_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2320_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v_infoState_2287_; lean_object* v_env_2288_; lean_object* v_nextMacroScope_2289_; lean_object* v_ngen_2290_; lean_object* v_auxDeclNGen_2291_; lean_object* v_traceState_2292_; lean_object* v_cache_2293_; lean_object* v_messages_2294_; lean_object* v_snapshotTasks_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2319_; 
v___x_2286_ = lean_st_ref_take(v___y_2268_);
v_infoState_2287_ = lean_ctor_get(v___x_2286_, 7);
v_env_2288_ = lean_ctor_get(v___x_2286_, 0);
v_nextMacroScope_2289_ = lean_ctor_get(v___x_2286_, 1);
v_ngen_2290_ = lean_ctor_get(v___x_2286_, 2);
v_auxDeclNGen_2291_ = lean_ctor_get(v___x_2286_, 3);
v_traceState_2292_ = lean_ctor_get(v___x_2286_, 4);
v_cache_2293_ = lean_ctor_get(v___x_2286_, 5);
v_messages_2294_ = lean_ctor_get(v___x_2286_, 6);
v_snapshotTasks_2295_ = lean_ctor_get(v___x_2286_, 8);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2297_ = v___x_2286_;
v_isShared_2298_ = v_isSharedCheck_2319_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_snapshotTasks_2295_);
lean_inc(v_infoState_2287_);
lean_inc(v_messages_2294_);
lean_inc(v_cache_2293_);
lean_inc(v_traceState_2292_);
lean_inc(v_auxDeclNGen_2291_);
lean_inc(v_ngen_2290_);
lean_inc(v_nextMacroScope_2289_);
lean_inc(v_env_2288_);
lean_dec(v___x_2286_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2319_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
uint8_t v_enabled_2299_; lean_object* v_assignment_2300_; lean_object* v_lazyAssignment_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2317_; 
v_enabled_2299_ = lean_ctor_get_uint8(v_infoState_2287_, sizeof(void*)*3);
v_assignment_2300_ = lean_ctor_get(v_infoState_2287_, 0);
v_lazyAssignment_2301_ = lean_ctor_get(v_infoState_2287_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_infoState_2287_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_infoState_2287_, 2);
lean_dec(v_unused_2318_);
v___x_2303_ = v_infoState_2287_;
v_isShared_2304_ = v_isSharedCheck_2317_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_lazyAssignment_2301_);
lean_inc(v_assignment_2300_);
lean_dec(v_infoState_2287_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2317_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2305_ = lean_box(0);
v___x_2306_ = l_Lean_PersistentArray_push___redArg(v_a_2275_, v_a_2282_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 2, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_assignment_2300_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_lazyAssignment_2301_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v___x_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2316_, sizeof(void*)*3, v_enabled_2299_);
v___x_2308_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 7, v___x_2308_);
v___x_2310_ = v___x_2297_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_env_2288_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_nextMacroScope_2289_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_ngen_2290_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_auxDeclNGen_2291_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_traceState_2292_);
lean_ctor_set(v_reuseFailAlloc_2315_, 5, v_cache_2293_);
lean_ctor_set(v_reuseFailAlloc_2315_, 6, v_messages_2294_);
lean_ctor_set(v_reuseFailAlloc_2315_, 7, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2315_, 8, v_snapshotTasks_2295_);
v___x_2310_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_st_ref_put(v___y_2268_, v___x_2310_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2305_);
v___x_2313_ = v___x_2284_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2305_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_a_2275_);
v_a_2321_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2281_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2281_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v___y_2329_, lean_object* v_mkInfoTree_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v_a_2336_, lean_object* v_a_x3f_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2329_, v_mkInfoTree_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v_a_2336_, v_a_x3f_2337_);
lean_dec(v_a_x3f_2337_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2329_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(lean_object* v_x_2340_, lean_object* v_mkInfoTree_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; lean_object* v_infoState_2350_; uint8_t v_enabled_2351_; 
v___x_2349_ = lean_st_ref_get(v___y_2347_);
v_infoState_2350_ = lean_ctor_get(v___x_2349_, 7);
lean_inc_ref(v_infoState_2350_);
lean_dec(v___x_2349_);
v_enabled_2351_ = lean_ctor_get_uint8(v_infoState_2350_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2350_);
if (v_enabled_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref(v_mkInfoTree_2341_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
v___x_2352_ = lean_apply_7(v_x_2340_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, lean_box(0));
return v___x_2352_;
}
else
{
lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v_r_2355_; 
v___x_2353_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_2347_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
v_r_2355_ = lean_apply_7(v_x_2340_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, lean_box(0));
if (lean_obj_tag(v_r_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2380_; 
v_a_2356_ = lean_ctor_get(v_r_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_r_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2358_ = v_r_2355_;
v_isShared_2359_ = v_isSharedCheck_2380_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v_r_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2380_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
lean_inc(v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 1);
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2347_, v_mkInfoTree_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v_a_2354_, v___x_2361_);
lean_dec_ref(v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2362_, 0);
lean_dec(v_unused_2370_);
v___x_2364_ = v___x_2362_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v___x_2362_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_a_2356_);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2356_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_a_2356_);
v_a_2371_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2362_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2362_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_a_2381_ = lean_ctor_get(v_r_2355_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v_r_2355_, 1);
v___x_2382_ = lean_box(0);
v___x_2383_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___lam__0(v___y_2347_, v_mkInfoTree_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v_a_2354_, v___x_2382_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2383_, 0);
lean_dec(v_unused_2391_);
v___x_2385_ = v___x_2383_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v___x_2383_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 0, v_a_2381_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2381_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_a_2381_);
v_a_2392_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2383_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2383_);
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
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg___boxed(lean_object* v_x_2400_, lean_object* v_mkInfoTree_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2400_, v_mkInfoTree_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(lean_object* v_stx_2410_, lean_object* v_output_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___f_2420_; lean_object* v___x_2421_; 
v___f_2420_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2420_, 0, v_stx_2410_);
lean_closure_set(v___f_2420_, 1, v_output_2411_);
v___x_2421_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_2412_, v___f_2420_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg___boxed(lean_object* v_stx_2422_, lean_object* v_output_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_2422_, v_output_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(lean_object* v_x_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
lean_inc_ref(v___y_2434_);
v___x_2442_ = lean_apply_8(v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, lean_box(0));
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed(lean_object* v_x_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0(v_x_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec_ref(v___y_2444_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(lean_object* v_beforeStx_2453_, lean_object* v_afterStx_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_inc_ref(v___y_2456_);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2464_, 0, v_x_2455_);
lean_closure_set(v___f_2464_, 1, v___y_2456_);
lean_inc(v_afterStx_2454_);
lean_inc(v_beforeStx_2453_);
v___x_2465_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withPushMacroExpansionStack___boxed), 11, 4);
lean_closure_set(v___x_2465_, 0, lean_box(0));
lean_closure_set(v___x_2465_, 1, v_beforeStx_2453_);
lean_closure_set(v___x_2465_, 2, v_afterStx_2454_);
lean_closure_set(v___x_2465_, 3, v___f_2464_);
v___x_2466_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_beforeStx_2453_, v_afterStx_2454_, v___x_2465_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
if (lean_obj_tag(v___x_2466_) == 0)
{
return v___x_2466_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg___boxed(lean_object* v_beforeStx_2475_, lean_object* v_afterStx_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_2475_, v_afterStx_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2486_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__1));
v___x_2490_ = l_String_toRawSubstring_x27(v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(lean_object* v_rhs_2512_, uint8_t v___x_2513_, lean_object* v_config_2514_, lean_object* v_a_2515_, uint8_t v___x_2516_, lean_object* v___x_2517_, lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v___f_2520_, lean_object* v___x_2521_, lean_object* v_body_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_term_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_ref_2539_; lean_object* v___y_2540_; lean_object* v_toCold_2546_; lean_object* v_ref_2547_; lean_object* v_quotContext_2548_; lean_object* v_currMacroScope_2549_; lean_object* v_ref_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_eq_x3f_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_toCold_2546_ = lean_ctor_get(v___y_2528_, 0);
v_ref_2547_ = lean_ctor_get(v___y_2528_, 2);
v_quotContext_2548_ = lean_ctor_get(v_toCold_2546_, 8);
v_currMacroScope_2549_ = lean_ctor_get(v_toCold_2546_, 9);
v_ref_2550_ = l_Lean_replaceRef(v_rhs_2512_, v_ref_2547_);
v___x_2551_ = l_Lean_SourceInfo_fromRef(v_ref_2550_, v___x_2513_);
lean_dec(v_ref_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__0));
lean_inc_n(v___x_2551_, 2);
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2, &l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__2);
v_eq_x3f_2555_ = lean_ctor_get(v_config_2514_, 0);
lean_inc(v_eq_x3f_2555_);
lean_dec_ref(v_config_2514_);
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__3));
lean_inc(v_currMacroScope_2549_);
lean_inc(v_quotContext_2548_);
v___x_2557_ = l_Lean_addMacroScope(v_quotContext_2548_, v___x_2556_, v_currMacroScope_2549_);
v___x_2558_ = lean_box(0);
lean_inc(v___x_2557_);
v___x_2559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2551_);
lean_ctor_set(v___x_2559_, 1, v___x_2554_);
lean_ctor_set(v___x_2559_, 2, v___x_2557_);
lean_ctor_set(v___x_2559_, 3, v___x_2558_);
v___x_2560_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__4));
lean_inc_ref(v___x_2519_);
lean_inc_ref(v___x_2518_);
lean_inc_ref(v___x_2517_);
v___x_2561_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node2(v___x_2551_, v___x_2561_, v___x_2553_, v___x_2559_);
if (lean_obj_tag(v_eq_x3f_2555_) == 1)
{
lean_object* v_val_2563_; lean_object* v___x_2564_; 
v_val_2563_ = lean_ctor_get(v_eq_x3f_2555_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v_eq_x3f_2555_, 1);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v_ref_2547_);
v___x_2564_ = lean_apply_9(v___f_2520_, v_ref_2547_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, lean_box(0));
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_n(v_a_2565_, 23);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2519_, 5);
lean_inc_ref_n(v___x_2518_, 5);
lean_inc_ref_n(v___x_2517_, 5);
v___x_2567_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_a_2565_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2565_);
lean_ctor_set(v___x_2570_, 1, v___x_2552_);
v___x_2571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2565_);
lean_ctor_set(v___x_2571_, 1, v___x_2554_);
lean_ctor_set(v___x_2571_, 2, v___x_2557_);
lean_ctor_set(v___x_2571_, 3, v___x_2558_);
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2565_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2565_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2577_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2576_);
v___x_2578_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2565_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2581_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_a_2565_);
lean_ctor_set(v___x_2582_, 1, v___x_2580_);
v___x_2583_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2584_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2565_);
lean_ctor_set(v___x_2585_, 1, v___x_2583_);
lean_ctor_set(v___x_2585_, 2, v___x_2584_);
v___x_2586_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2587_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_2589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_a_2565_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Lean_Syntax_node2(v_a_2565_, v___x_2583_, v_val_2563_, v___x_2589_);
v___x_2591_ = l_Lean_Syntax_node2(v_a_2565_, v___x_2587_, v___x_2590_, v___x_2562_);
v___x_2592_ = l_Lean_Syntax_node1(v_a_2565_, v___x_2583_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_a_2565_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2596_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2595_);
v___x_2597_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2598_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2597_);
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_a_2565_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_Syntax_node1(v_a_2565_, v___x_2583_, v___x_2521_);
v___x_2602_ = l_Lean_Syntax_node1(v_a_2565_, v___x_2583_, v___x_2601_);
v___x_2603_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2565_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_Syntax_node4(v_a_2565_, v___x_2598_, v___x_2600_, v___x_2602_, v___x_2604_, v_body_2522_);
v___x_2606_ = l_Lean_Syntax_node1(v_a_2565_, v___x_2583_, v___x_2605_);
v___x_2607_ = l_Lean_Syntax_node1(v_a_2565_, v___x_2596_, v___x_2606_);
lean_inc_ref(v___x_2585_);
v___x_2608_ = l_Lean_Syntax_node6(v_a_2565_, v___x_2581_, v___x_2582_, v___x_2585_, v___x_2585_, v___x_2592_, v___x_2594_, v___x_2607_);
lean_inc_ref(v___x_2575_);
lean_inc_ref(v___x_2571_);
lean_inc_ref(v___x_2570_);
v___x_2609_ = l_Lean_Syntax_node5(v_a_2565_, v___x_2577_, v___x_2579_, v___x_2570_, v___x_2571_, v___x_2575_, v___x_2608_);
v___x_2610_ = l_Lean_Syntax_node7(v_a_2565_, v___x_2567_, v___x_2569_, v___x_2570_, v___x_2571_, v___x_2573_, v_rhs_2512_, v___x_2575_, v___x_2609_);
lean_inc(v_ref_2547_);
v_term_2532_ = v___x_2610_;
v___y_2533_ = v___y_2523_;
v___y_2534_ = v___y_2524_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v___y_2538_ = v___y_2528_;
v_ref_2539_ = v_ref_2547_;
v___y_2540_ = v___y_2529_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_val_2563_);
lean_dec(v___x_2562_);
lean_dec(v___x_2557_);
lean_dec(v_body_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v_a_2515_);
lean_dec(v_rhs_2512_);
v_a_2611_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2564_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2564_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v___x_2619_; 
lean_dec(v_eq_x3f_2555_);
lean_inc_ref(v_a_2515_);
v___x_2619_ = l_Lean_Elab_Term_exprToSyntax(v_a_2515_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v_ref_2547_);
v___x_2621_ = lean_apply_9(v___f_2520_, v_ref_2547_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, lean_box(0));
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc_n(v_a_2622_, 32);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__5));
lean_inc_ref_n(v___x_2519_, 8);
lean_inc_ref_n(v___x_2518_, 8);
lean_inc_ref_n(v___x_2517_, 8);
v___x_2624_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__6));
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_a_2622_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_a_2622_);
lean_ctor_set(v___x_2627_, 1, v___x_2552_);
v___x_2628_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2622_);
lean_ctor_set(v___x_2628_, 1, v___x_2554_);
lean_ctor_set(v___x_2628_, 2, v___x_2557_);
lean_ctor_set(v___x_2628_, 3, v___x_2558_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_2630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_a_2622_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_2632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_a_2622_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__8));
v___x_2634_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2633_);
v___x_2635_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__9));
v___x_2636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_a_2622_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_2638_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2637_);
v___x_2639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_a_2622_);
lean_ctor_set(v___x_2639_, 1, v___x_2637_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_2641_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_2642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2642_, 0, v_a_2622_);
lean_ctor_set(v___x_2642_, 1, v___x_2640_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__17));
v___x_2644_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2643_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
v___x_2646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2622_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_a_2622_);
lean_ctor_set(v___x_2647_, 1, v___x_2643_);
v___x_2648_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__18));
v___x_2649_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2648_);
v___x_2650_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__19));
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_a_2622_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__20));
v___x_2653_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2652_);
v___x_2654_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_2655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_a_2622_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2653_, v___x_2655_);
v___x_2657_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__22));
v___x_2659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_a_2622_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_inc_ref_n(v___x_2642_, 2);
v___x_2660_ = l_Lean_Syntax_node5(v_a_2622_, v___x_2649_, v___x_2651_, v___x_2657_, v___x_2642_, v___x_2659_, v_a_2620_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_2662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2662_, 0, v_a_2622_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
lean_inc_ref(v___x_2630_);
v___x_2663_ = l_Lean_Syntax_node5(v_a_2622_, v___x_2644_, v___x_2646_, v___x_2647_, v___x_2630_, v___x_2660_, v___x_2662_);
v___x_2664_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2663_);
v___x_2665_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__11));
v___x_2666_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node2(v_a_2622_, v___x_2666_, v___x_2642_, v___x_2562_);
v___x_2668_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2667_);
v___x_2669_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_2670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_a_2622_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__13));
v___x_2672_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2671_);
v___x_2673_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__14));
v___x_2674_ = l_Lean_Name_mkStr4(v___x_2517_, v___x_2518_, v___x_2519_, v___x_2673_);
v___x_2675_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_2676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_a_2622_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2521_);
v___x_2678_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2677_);
v___x_2679_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_2680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_a_2622_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_Syntax_node4(v_a_2622_, v___x_2674_, v___x_2676_, v___x_2678_, v___x_2680_, v_body_2522_);
v___x_2682_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2640_, v___x_2681_);
v___x_2683_ = l_Lean_Syntax_node1(v_a_2622_, v___x_2672_, v___x_2682_);
v___x_2684_ = l_Lean_Syntax_node6(v_a_2622_, v___x_2638_, v___x_2639_, v___x_2642_, v___x_2664_, v___x_2668_, v___x_2670_, v___x_2683_);
lean_inc_ref(v___x_2632_);
lean_inc_ref(v___x_2628_);
lean_inc_ref(v___x_2627_);
v___x_2685_ = l_Lean_Syntax_node5(v_a_2622_, v___x_2634_, v___x_2636_, v___x_2627_, v___x_2628_, v___x_2632_, v___x_2684_);
v___x_2686_ = l_Lean_Syntax_node7(v_a_2622_, v___x_2624_, v___x_2626_, v___x_2627_, v___x_2628_, v___x_2630_, v_rhs_2512_, v___x_2632_, v___x_2685_);
lean_inc(v_ref_2547_);
v_term_2532_ = v___x_2686_;
v___y_2533_ = v___y_2523_;
v___y_2534_ = v___y_2524_;
v___y_2535_ = v___y_2525_;
v___y_2536_ = v___y_2526_;
v___y_2537_ = v___y_2527_;
v___y_2538_ = v___y_2528_;
v_ref_2539_ = v_ref_2547_;
v___y_2540_ = v___y_2529_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_a_2620_);
lean_dec(v___x_2562_);
lean_dec(v___x_2557_);
lean_dec(v_body_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v_a_2515_);
lean_dec(v_rhs_2512_);
v_a_2687_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2621_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2621_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v___x_2562_);
lean_dec(v___x_2557_);
lean_dec(v_body_2522_);
lean_dec(v___x_2521_);
lean_dec_ref(v___f_2520_);
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v___x_2517_);
lean_dec_ref(v_a_2515_);
lean_dec(v_rhs_2512_);
v_a_2695_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2619_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2619_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
v___jp_2531_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; 
v___x_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_a_2515_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_box(v___x_2516_);
lean_inc(v_term_2532_);
v___f_2544_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__5___boxed), 12, 4);
lean_closure_set(v___f_2544_, 0, v_term_2532_);
lean_closure_set(v___f_2544_, 1, v___x_2541_);
lean_closure_set(v___f_2544_, 2, v___x_2543_);
lean_closure_set(v___f_2544_, 3, v___x_2542_);
v___x_2545_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_ref_2539_, v_term_2532_, v___f_2544_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2540_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed(lean_object** _args){
lean_object* v_rhs_2703_ = _args[0];
lean_object* v___x_2704_ = _args[1];
lean_object* v_config_2705_ = _args[2];
lean_object* v_a_2706_ = _args[3];
lean_object* v___x_2707_ = _args[4];
lean_object* v___x_2708_ = _args[5];
lean_object* v___x_2709_ = _args[6];
lean_object* v___x_2710_ = _args[7];
lean_object* v___f_2711_ = _args[8];
lean_object* v___x_2712_ = _args[9];
lean_object* v_body_2713_ = _args[10];
lean_object* v___y_2714_ = _args[11];
lean_object* v___y_2715_ = _args[12];
lean_object* v___y_2716_ = _args[13];
lean_object* v___y_2717_ = _args[14];
lean_object* v___y_2718_ = _args[15];
lean_object* v___y_2719_ = _args[16];
lean_object* v___y_2720_ = _args[17];
lean_object* v___y_2721_ = _args[18];
_start:
{
uint8_t v___x_89629__boxed_2722_; uint8_t v___x_89631__boxed_2723_; lean_object* v_res_2724_; 
v___x_89629__boxed_2722_ = lean_unbox(v___x_2704_);
v___x_89631__boxed_2723_ = lean_unbox(v___x_2707_);
v_res_2724_ = l_Lean_Elab_Do_elabDoLetOrReassign___lam__6(v_rhs_2703_, v___x_89629__boxed_2722_, v_config_2705_, v_a_2706_, v___x_89631__boxed_2723_, v___x_2708_, v___x_2709_, v___x_2710_, v___f_2711_, v___x_2712_, v_body_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2724_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2725_; double v___x_2726_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = lean_float_of_nat(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(lean_object* v_cls_2729_, lean_object* v_msg_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_ref_2736_; lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2782_; 
v_ref_2736_ = lean_ctor_get(v___y_2733_, 2);
v___x_2737_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0_spec__1(v_msg_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2782_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2782_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v_traceState_2743_; lean_object* v_env_2744_; lean_object* v_nextMacroScope_2745_; lean_object* v_ngen_2746_; lean_object* v_auxDeclNGen_2747_; lean_object* v_cache_2748_; lean_object* v_messages_2749_; lean_object* v_infoState_2750_; lean_object* v_snapshotTasks_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2781_; 
v___x_2742_ = lean_st_ref_take(v___y_2734_);
v_traceState_2743_ = lean_ctor_get(v___x_2742_, 4);
v_env_2744_ = lean_ctor_get(v___x_2742_, 0);
v_nextMacroScope_2745_ = lean_ctor_get(v___x_2742_, 1);
v_ngen_2746_ = lean_ctor_get(v___x_2742_, 2);
v_auxDeclNGen_2747_ = lean_ctor_get(v___x_2742_, 3);
v_cache_2748_ = lean_ctor_get(v___x_2742_, 5);
v_messages_2749_ = lean_ctor_get(v___x_2742_, 6);
v_infoState_2750_ = lean_ctor_get(v___x_2742_, 7);
v_snapshotTasks_2751_ = lean_ctor_get(v___x_2742_, 8);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2753_ = v___x_2742_;
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snapshotTasks_2751_);
lean_inc(v_infoState_2750_);
lean_inc(v_messages_2749_);
lean_inc(v_cache_2748_);
lean_inc(v_traceState_2743_);
lean_inc(v_auxDeclNGen_2747_);
lean_inc(v_ngen_2746_);
lean_inc(v_nextMacroScope_2745_);
lean_inc(v_env_2744_);
lean_dec(v___x_2742_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2781_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
uint64_t v_tid_2755_; lean_object* v_traces_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2780_; 
v_tid_2755_ = lean_ctor_get_uint64(v_traceState_2743_, sizeof(void*)*1);
v_traces_2756_ = lean_ctor_get(v_traceState_2743_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_traceState_2743_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2758_ = v_traceState_2743_;
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_traces_2756_);
lean_dec(v_traceState_2743_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; double v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__0);
v___x_2763_ = 0;
v___x_2764_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2765_, 0, v_cls_2729_);
lean_ctor_set(v___x_2765_, 1, v___x_2761_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
lean_ctor_set_float(v___x_2765_, sizeof(void*)*3, v___x_2762_);
lean_ctor_set_float(v___x_2765_, sizeof(void*)*3 + 8, v___x_2762_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*3 + 16, v___x_2763_);
v___x_2766_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___closed__1));
v___x_2767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v_a_2738_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
lean_inc(v_ref_2736_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_ref_2736_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Lean_PersistentArray_push___redArg(v_traces_2756_, v___x_2768_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2769_);
v___x_2771_ = v___x_2758_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2769_);
lean_ctor_set_uint64(v_reuseFailAlloc_2779_, sizeof(void*)*1, v_tid_2755_);
v___x_2771_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 4, v___x_2771_);
v___x_2773_ = v___x_2753_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_env_2744_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_nextMacroScope_2745_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_ngen_2746_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_auxDeclNGen_2747_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v_cache_2748_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_messages_2749_);
lean_ctor_set(v_reuseFailAlloc_2778_, 7, v_infoState_2750_);
lean_ctor_set(v_reuseFailAlloc_2778_, 8, v_snapshotTasks_2751_);
v___x_2773_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_st_ref_put(v___y_2734_, v___x_2773_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2760_);
v___x_2776_ = v___x_2740_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2760_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg___boxed(lean_object* v_cls_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_2783_, v_msg_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(lean_object* v_env_2791_, lean_object* v_options_2792_, lean_object* v_currNamespace_2793_, lean_object* v_openDecls_2794_, lean_object* v_n_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = l_Lean_ResolveName_resolveGlobalName(v_env_2791_, v_options_2792_, v_currNamespace_2793_, v_openDecls_2794_, v_n_2795_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___y_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed(lean_object* v_env_2800_, lean_object* v_options_2801_, lean_object* v_currNamespace_2802_, lean_object* v_openDecls_2803_, lean_object* v_n_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4(v_env_2800_, v_options_2801_, v_currNamespace_2802_, v_openDecls_2803_, v_n_2804_, v___y_2805_, v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v_options_2801_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(lean_object* v_env_2808_, lean_object* v_currNamespace_2809_, lean_object* v_openDecls_2810_, lean_object* v_n_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = l_Lean_ResolveName_resolveNamespace(v_env_2808_, v_currNamespace_2809_, v_openDecls_2810_, v_n_2811_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed(lean_object* v_env_2816_, lean_object* v_currNamespace_2817_, lean_object* v_openDecls_2818_, lean_object* v_n_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2(v_env_2816_, v_currNamespace_2817_, v_openDecls_2818_, v_n_2819_, v___y_2820_, v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(lean_object* v_x_2823_, lean_object* v___y_2824_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2825_ = lean_ctor_get(v_x_2823_, 0);
lean_inc(v_a_2825_);
v___x_2826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2825_);
lean_ctor_set(v___x_2826_, 1, v___y_2824_);
return v___x_2826_;
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v_x_2823_, 0);
lean_inc(v_a_2827_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2827_);
lean_ctor_set(v___x_2828_, 1, v___y_2824_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg___boxed(lean_object* v_x_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_2829_, v___y_2830_);
lean_dec_ref(v_x_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(lean_object* v_env_2832_, lean_object* v_stx_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2832_, v_stx_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
if (lean_obj_tag(v_a_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2846_; 
v_a_2838_ = lean_ctor_get(v___x_2836_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2847_);
v___x_2840_ = v___x_2836_;
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2836_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_box(0);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2842_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_a_2838_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_val_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2876_; 
v_val_2848_ = lean_ctor_get(v_a_2837_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_a_2837_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2850_ = v_a_2837_;
v_isShared_2851_ = v_isSharedCheck_2876_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_val_2848_);
lean_dec(v_a_2837_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2876_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_snd_2852_; 
v_snd_2852_ = lean_ctor_get(v_val_2848_, 1);
lean_inc(v_snd_2852_);
lean_dec(v_val_2848_);
if (lean_obj_tag(v_snd_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2850_);
v_a_2853_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2836_, 2);
v_a_2854_ = lean_ctor_get(v_snd_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_snd_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v_snd_2852_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v_snd_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_2859_, v_a_2853_);
lean_dec_ref(v___x_2859_);
return v___x_2860_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2875_; 
v_a_2863_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2836_, 2);
v_a_2864_ = lean_ctor_get(v_snd_2852_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_snd_2852_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2866_ = v_snd_2852_;
v_isShared_2867_ = v_isSharedCheck_2875_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v_snd_2852_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2875_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_a_2864_);
v___x_2869_ = v___x_2850_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2869_);
v___x_2871_ = v___x_2866_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v___x_2871_, v_a_2863_);
lean_dec_ref(v___x_2871_);
return v___x_2872_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_a_2877_ = lean_ctor_get(v___x_2836_, 0);
v_a_2878_ = lean_ctor_get(v___x_2836_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2836_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_inc(v_a_2877_);
lean_dec(v___x_2836_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2877_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed(lean_object* v_env_2886_, lean_object* v_stx_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0(v_env_2886_, v_stx_2887_, v___y_2888_, v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2890_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = l_Lean_maxRecDepthErrorMessage;
v___x_2897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__3);
v___x_2899_ = l_Lean_MessageData_ofFormat(v___x_2898_);
return v___x_2899_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__4);
v___x_2901_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__2));
v___x_2902_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___x_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(lean_object* v_ref_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___closed__5);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v_ref_2903_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(lean_object* v_keys_2911_, lean_object* v_i_2912_, lean_object* v_k_2913_){
_start:
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = lean_array_get_size(v_keys_2911_);
v___x_2915_ = lean_nat_dec_lt(v_i_2912_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v_i_2912_);
return v___x_2915_;
}
else
{
lean_object* v_k_x27_2916_; uint8_t v___x_2917_; 
v_k_x27_2916_ = lean_array_fget_borrowed(v_keys_2911_, v_i_2912_);
v___x_2917_ = l_Lean_instBEqExtraModUse_beq(v_k_2913_, v_k_x27_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_unsigned_to_nat(1u);
v___x_2919_ = lean_nat_add(v_i_2912_, v___x_2918_);
lean_dec(v_i_2912_);
v_i_2912_ = v___x_2919_;
goto _start;
}
else
{
lean_dec(v_i_2912_);
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg___boxed(lean_object* v_keys_2921_, lean_object* v_i_2922_, lean_object* v_k_2923_){
_start:
{
uint8_t v_res_2924_; lean_object* v_r_2925_; 
v_res_2924_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_2921_, v_i_2922_, v_k_2923_);
lean_dec_ref(v_k_2923_);
lean_dec_ref(v_keys_2921_);
v_r_2925_ = lean_box(v_res_2924_);
return v_r_2925_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(lean_object* v_x_2926_, size_t v_x_2927_, lean_object* v_x_2928_){
_start:
{
if (lean_obj_tag(v_x_2926_) == 0)
{
lean_object* v_es_2929_; lean_object* v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; lean_object* v_j_2933_; lean_object* v___x_2934_; 
v_es_2929_ = lean_ctor_get(v_x_2926_, 0);
v___x_2930_ = lean_box(2);
v___x_2931_ = ((size_t)31ULL);
v___x_2932_ = lean_usize_land(v_x_2927_, v___x_2931_);
v_j_2933_ = lean_usize_to_nat(v___x_2932_);
v___x_2934_ = lean_array_get_borrowed(v___x_2930_, v_es_2929_, v_j_2933_);
lean_dec(v_j_2933_);
switch(lean_obj_tag(v___x_2934_))
{
case 0:
{
lean_object* v_key_2935_; uint8_t v___x_2936_; 
v_key_2935_ = lean_ctor_get(v___x_2934_, 0);
v___x_2936_ = l_Lean_instBEqExtraModUse_beq(v_x_2928_, v_key_2935_);
return v___x_2936_;
}
case 1:
{
lean_object* v_node_2937_; size_t v___x_2938_; size_t v___x_2939_; 
v_node_2937_ = lean_ctor_get(v___x_2934_, 0);
v___x_2938_ = ((size_t)5ULL);
v___x_2939_ = lean_usize_shift_right(v_x_2927_, v___x_2938_);
v_x_2926_ = v_node_2937_;
v_x_2927_ = v___x_2939_;
goto _start;
}
default: 
{
uint8_t v___x_2941_; 
v___x_2941_ = 0;
return v___x_2941_;
}
}
}
else
{
lean_object* v_ks_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v_ks_2942_ = lean_ctor_get(v_x_2926_, 0);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_ks_2942_, v___x_2943_, v_x_2928_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg___boxed(lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
size_t v_x_90327__boxed_2948_; uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_x_90327__boxed_2948_ = lean_unbox_usize(v_x_2946_);
lean_dec(v_x_2946_);
v_res_2949_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2945_, v_x_90327__boxed_2948_, v_x_2947_);
lean_dec_ref(v_x_2947_);
lean_dec_ref(v_x_2945_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
uint64_t v___x_2953_; size_t v___x_2954_; uint8_t v___x_2955_; 
v___x_2953_ = l_Lean_instHashableExtraModUse_hash(v_x_2952_);
v___x_2954_ = lean_uint64_to_usize(v___x_2953_);
v___x_2955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_2951_, v___x_2954_, v_x_2952_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg___boxed(lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
uint8_t v_res_2958_; lean_object* v_r_2959_; 
v_res_2958_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_2956_, v_x_2957_);
lean_dec_ref(v_x_2957_);
lean_dec_ref(v_x_2956_);
v_r_2959_ = lean_box(v_res_2958_);
return v_r_2959_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0(void){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2960_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1(void){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2961_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__1);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__2);
v___x_2967_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
lean_ctor_set(v___x_2967_, 3, v___x_2966_);
lean_ctor_set(v___x_2967_, 4, v___x_2966_);
lean_ctor_set(v___x_2967_, 5, v___x_2966_);
return v___x_2967_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__7));
v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
return v___x_2973_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10(void){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__9));
v___x_2976_ = l_Lean_stringToMessageData(v___x_2975_);
return v___x_2976_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__22));
v___x_2978_ = l_Lean_stringToMessageData(v___x_2977_);
return v___x_2978_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14(void){
_start:
{
lean_object* v_cls_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_cls_2982_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_2983_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_2984_ = l_Lean_Name_append(v___x_2983_, v_cls_2982_);
return v___x_2984_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__15));
v___x_2987_ = l_Lean_stringToMessageData(v___x_2986_);
return v___x_2987_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__17));
v___x_2990_ = l_Lean_stringToMessageData(v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(lean_object* v_mod_2995_, uint8_t v_isMeta_2996_, lean_object* v_hint_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v_env_3008_; uint8_t v_isExporting_3009_; lean_object* v_entry_3010_; lean_object* v___x_3011_; lean_object* v_env_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3006_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__0);
v___x_3007_ = lean_st_ref_get(v___y_3004_);
v_env_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3007_);
v_isExporting_3009_ = lean_ctor_get_uint8(v_env_3008_, sizeof(void*)*8);
lean_dec_ref(v_env_3008_);
lean_inc(v_mod_2995_);
v_entry_3010_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3010_, 0, v_mod_2995_);
lean_ctor_set_uint8(v_entry_3010_, sizeof(void*)*1, v_isExporting_3009_);
lean_ctor_set_uint8(v_entry_3010_, sizeof(void*)*1 + 1, v_isMeta_2996_);
v___x_3011_ = lean_st_ref_get(v___y_3004_);
v_env_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc_ref(v_env_3012_);
lean_dec(v___x_3011_);
v___x_3013_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3014_ = lean_box(1);
v___x_3015_ = lean_box(0);
v___x_3058_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3006_, v___x_3013_, v_env_3012_, v___x_3014_, v___x_3015_);
v___x_3059_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v___x_3058_, v_entry_3010_);
lean_dec(v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v_toCold_3060_; lean_object* v_options_3061_; uint8_t v_hasTrace_3062_; 
v_toCold_3060_ = lean_ctor_get(v___y_3003_, 0);
v_options_3061_ = lean_ctor_get(v_toCold_3060_, 2);
v_hasTrace_3062_ = lean_ctor_get_uint8(v_options_3061_, sizeof(void*)*1);
if (v_hasTrace_3062_ == 0)
{
lean_dec(v_hint_2997_);
lean_dec(v_mod_2995_);
v___y_3017_ = v___y_3002_;
v___y_3018_ = v___y_3004_;
goto v___jp_3016_;
}
else
{
lean_object* v_inheritedTraceOptions_3063_; lean_object* v_cls_3064_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_inheritedTraceOptions_3063_ = lean_ctor_get(v_toCold_3060_, 11);
v_cls_3064_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__6));
v___x_3084_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__14);
v___x_3085_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3063_, v_options_3061_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_dec(v_hint_2997_);
lean_dec(v_mod_2995_);
v___y_3017_ = v___y_3002_;
v___y_3018_ = v___y_3004_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3086_; lean_object* v___y_3088_; 
v___x_3086_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__16);
if (v_isExporting_3009_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__21));
v___y_3088_ = v___x_3095_;
goto v___jp_3087_;
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__22));
v___y_3088_ = v___x_3096_;
goto v___jp_3087_;
}
v___jp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_inc_ref(v___y_3088_);
v___x_3089_ = l_Lean_stringToMessageData(v___y_3088_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3086_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__18);
v___x_3092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
if (v_isMeta_2996_ == 0)
{
lean_object* v___x_3093_; 
v___x_3093_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__19));
v___y_3071_ = v___x_3092_;
v___y_3072_ = v___x_3093_;
goto v___jp_3070_;
}
else
{
lean_object* v___x_3094_; 
v___x_3094_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__20));
v___y_3071_ = v___x_3092_;
v___y_3072_ = v___x_3094_;
goto v___jp_3070_;
}
}
}
v___jp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3066_);
lean_ctor_set(v___x_3068_, 1, v___y_3067_);
v___x_3069_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3064_, v___x_3068_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref_known(v___x_3069_, 1);
v___y_3017_ = v___y_3002_;
v___y_3018_ = v___y_3004_;
goto v___jp_3016_;
}
else
{
lean_dec_ref_known(v_entry_3010_, 1);
return v___x_3069_;
}
}
v___jp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
lean_inc_ref(v___y_3072_);
v___x_3073_ = l_Lean_stringToMessageData(v___y_3072_);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___y_3071_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__8);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Lean_MessageData_ofName(v_mod_2995_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_Name_isAnonymous(v_hint_2997_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__10);
v___x_3081_ = l_Lean_MessageData_ofName(v_hint_2997_);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___y_3066_ = v___x_3078_;
v___y_3067_ = v___x_3082_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3083_; 
lean_dec(v_hint_2997_);
v___x_3083_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__11);
v___y_3066_ = v___x_3078_;
v___y_3067_ = v___x_3083_;
goto v___jp_3065_;
}
}
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_dec_ref_known(v_entry_3010_, 1);
lean_dec(v_hint_2997_);
lean_dec(v_mod_2995_);
v___x_3097_ = lean_box(0);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
return v___x_3098_;
}
v___jp_3016_:
{
lean_object* v___x_3019_; lean_object* v_toEnvExtension_3020_; lean_object* v_env_3021_; lean_object* v_nextMacroScope_3022_; lean_object* v_ngen_3023_; lean_object* v_auxDeclNGen_3024_; lean_object* v_traceState_3025_; lean_object* v_messages_3026_; lean_object* v_infoState_3027_; lean_object* v_snapshotTasks_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3056_; 
v___x_3019_ = lean_st_ref_take(v___y_3018_);
v_toEnvExtension_3020_ = lean_ctor_get(v___x_3013_, 0);
v_env_3021_ = lean_ctor_get(v___x_3019_, 0);
v_nextMacroScope_3022_ = lean_ctor_get(v___x_3019_, 1);
v_ngen_3023_ = lean_ctor_get(v___x_3019_, 2);
v_auxDeclNGen_3024_ = lean_ctor_get(v___x_3019_, 3);
v_traceState_3025_ = lean_ctor_get(v___x_3019_, 4);
v_messages_3026_ = lean_ctor_get(v___x_3019_, 6);
v_infoState_3027_ = lean_ctor_get(v___x_3019_, 7);
v_snapshotTasks_3028_ = lean_ctor_get(v___x_3019_, 8);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3019_, 5);
lean_dec(v_unused_3057_);
v___x_3030_ = v___x_3019_;
v_isShared_3031_ = v_isSharedCheck_3056_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snapshotTasks_3028_);
lean_inc(v_infoState_3027_);
lean_inc(v_messages_3026_);
lean_inc(v_traceState_3025_);
lean_inc(v_auxDeclNGen_3024_);
lean_inc(v_ngen_3023_);
lean_inc(v_nextMacroScope_3022_);
lean_inc(v_env_3021_);
lean_dec(v___x_3019_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3056_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v_asyncMode_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v_asyncMode_3032_ = lean_ctor_get(v_toEnvExtension_3020_, 2);
v___x_3033_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3013_, v_env_3021_, v_entry_3010_, v_asyncMode_3032_, v___x_3015_);
v___x_3034_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__3);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 5, v___x_3034_);
lean_ctor_set(v___x_3030_, 0, v___x_3033_);
v___x_3036_ = v___x_3030_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_nextMacroScope_3022_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_ngen_3023_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_auxDeclNGen_3024_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_traceState_3025_);
lean_ctor_set(v_reuseFailAlloc_3055_, 5, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3055_, 6, v_messages_3026_);
lean_ctor_set(v_reuseFailAlloc_3055_, 7, v_infoState_3027_);
lean_ctor_set(v_reuseFailAlloc_3055_, 8, v_snapshotTasks_3028_);
v___x_3036_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v_mctx_3039_; lean_object* v_zetaDeltaFVarIds_3040_; lean_object* v_postponed_3041_; lean_object* v_diag_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3053_; 
v___x_3037_ = lean_st_ref_put(v___y_3018_, v___x_3036_);
v___x_3038_ = lean_st_ref_take(v___y_3017_);
v_mctx_3039_ = lean_ctor_get(v___x_3038_, 0);
v_zetaDeltaFVarIds_3040_ = lean_ctor_get(v___x_3038_, 2);
v_postponed_3041_ = lean_ctor_get(v___x_3038_, 3);
v_diag_3042_ = lean_ctor_get(v___x_3038_, 4);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3053_ == 0)
{
lean_object* v_unused_3054_; 
v_unused_3054_ = lean_ctor_get(v___x_3038_, 1);
lean_dec(v_unused_3054_);
v___x_3044_ = v___x_3038_;
v_isShared_3045_ = v_isSharedCheck_3053_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_diag_3042_);
lean_inc(v_postponed_3041_);
lean_inc(v_zetaDeltaFVarIds_3040_);
lean_inc(v_mctx_3039_);
lean_dec(v___x_3038_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3053_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__4);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3047_);
v___x_3049_ = v___x_3044_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_mctx_3039_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_zetaDeltaFVarIds_3040_);
lean_ctor_set(v_reuseFailAlloc_3052_, 3, v_postponed_3041_);
lean_ctor_set(v_reuseFailAlloc_3052_, 4, v_diag_3042_);
v___x_3049_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_st_ref_put(v___y_3017_, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3046_);
return v___x_3051_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___boxed(lean_object* v_mod_3099_, lean_object* v_isMeta_3100_, lean_object* v_hint_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
uint8_t v_isMeta_boxed_3110_; lean_object* v_res_3111_; 
v_isMeta_boxed_3110_ = lean_unbox(v_isMeta_3100_);
v_res_3111_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_mod_3099_, v_isMeta_boxed_3110_, v_hint_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(lean_object* v___x_3112_, lean_object* v_declName_3113_, lean_object* v_as_3114_, size_t v_sz_3115_, size_t v_i_3116_, lean_object* v_b_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_usize_dec_lt(v_i_3116_, v_sz_3115_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec(v_declName_3113_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_b_3117_);
return v___x_3127_;
}
else
{
lean_object* v___x_3128_; lean_object* v_modules_3129_; lean_object* v___x_3130_; lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v_toImport_3133_; lean_object* v_module_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; 
v___x_3128_ = l_Lean_Environment_header(v___x_3112_);
v_modules_3129_ = lean_ctor_get(v___x_3128_, 3);
lean_inc_ref(v_modules_3129_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3131_ = lean_array_uget_borrowed(v_as_3114_, v_i_3116_);
v___x_3132_ = lean_array_get(v___x_3130_, v_modules_3129_, v_a_3131_);
lean_dec_ref(v_modules_3129_);
v_toImport_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc_ref(v_toImport_3133_);
lean_dec(v___x_3132_);
v_module_3134_ = lean_ctor_get(v_toImport_3133_, 0);
lean_inc(v_module_3134_);
lean_dec_ref(v_toImport_3133_);
v___x_3135_ = lean_box(0);
v___x_3136_ = 0;
lean_inc(v_declName_3113_);
v___x_3137_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3134_, v___x_3136_, v_declName_3113_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
if (lean_obj_tag(v___x_3137_) == 0)
{
size_t v___x_3138_; size_t v___x_3139_; 
lean_dec_ref_known(v___x_3137_, 1);
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3116_, v___x_3138_);
v_i_3116_ = v___x_3139_;
v_b_3117_ = v___x_3135_;
goto _start;
}
else
{
lean_dec(v_declName_3113_);
return v___x_3137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17___boxed(lean_object* v___x_3141_, lean_object* v_declName_3142_, lean_object* v_as_3143_, lean_object* v_sz_3144_, lean_object* v_i_3145_, lean_object* v_b_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
size_t v_sz_boxed_3155_; size_t v_i_boxed_3156_; lean_object* v_res_3157_; 
v_sz_boxed_3155_ = lean_unbox_usize(v_sz_3144_);
lean_dec(v_sz_3144_);
v_i_boxed_3156_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_res_3157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v___x_3141_, v_declName_3142_, v_as_3143_, v_sz_boxed_3155_, v_i_boxed_3156_, v_b_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_as_3143_);
lean_dec_ref(v___x_3141_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(lean_object* v_a_3158_, lean_object* v_x_3159_){
_start:
{
if (lean_obj_tag(v_x_3159_) == 0)
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_box(0);
return v___x_3160_;
}
else
{
lean_object* v_key_3161_; lean_object* v_value_3162_; lean_object* v_tail_3163_; uint8_t v___x_3164_; 
v_key_3161_ = lean_ctor_get(v_x_3159_, 0);
v_value_3162_ = lean_ctor_get(v_x_3159_, 1);
v_tail_3163_ = lean_ctor_get(v_x_3159_, 2);
v___x_3164_ = lean_name_eq(v_key_3161_, v_a_3158_);
if (v___x_3164_ == 0)
{
v_x_3159_ = v_tail_3163_;
goto _start;
}
else
{
lean_object* v___x_3166_; 
lean_inc(v_value_3162_);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_value_3162_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg___boxed(lean_object* v_a_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3167_, v_x_3168_);
lean_dec(v_x_3168_);
lean_dec(v_a_3167_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(lean_object* v_m_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_buckets_3172_; lean_object* v___x_3173_; uint64_t v___y_3175_; 
v_buckets_3172_ = lean_ctor_get(v_m_3170_, 1);
v___x_3173_ = lean_array_get_size(v_buckets_3172_);
if (lean_obj_tag(v_a_3171_) == 0)
{
uint64_t v___x_3189_; 
v___x_3189_ = 1723ULL;
v___y_3175_ = v___x_3189_;
goto v___jp_3174_;
}
else
{
uint64_t v_hash_3190_; 
v_hash_3190_ = lean_ctor_get_uint64(v_a_3171_, sizeof(void*)*2);
v___y_3175_ = v_hash_3190_;
goto v___jp_3174_;
}
v___jp_3174_:
{
uint64_t v___x_3176_; uint64_t v___x_3177_; uint64_t v_fold_3178_; uint64_t v___x_3179_; uint64_t v___x_3180_; uint64_t v___x_3181_; size_t v___x_3182_; size_t v___x_3183_; size_t v___x_3184_; size_t v___x_3185_; size_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3176_ = 32ULL;
v___x_3177_ = lean_uint64_shift_right(v___y_3175_, v___x_3176_);
v_fold_3178_ = lean_uint64_xor(v___y_3175_, v___x_3177_);
v___x_3179_ = 16ULL;
v___x_3180_ = lean_uint64_shift_right(v_fold_3178_, v___x_3179_);
v___x_3181_ = lean_uint64_xor(v_fold_3178_, v___x_3180_);
v___x_3182_ = lean_uint64_to_usize(v___x_3181_);
v___x_3183_ = lean_usize_of_nat(v___x_3173_);
v___x_3184_ = ((size_t)1ULL);
v___x_3185_ = lean_usize_sub(v___x_3183_, v___x_3184_);
v___x_3186_ = lean_usize_land(v___x_3182_, v___x_3185_);
v___x_3187_ = lean_array_uget_borrowed(v_buckets_3172_, v___x_3186_);
v___x_3188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_3171_, v___x_3187_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg___boxed(lean_object* v_m_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_m_3191_);
return v_res_3193_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(lean_object* v_declName_3197_, uint8_t v_isMeta_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_env_3212_; lean_object* v___y_3214_; lean_object* v___x_3227_; 
v___x_3207_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__0);
v___x_3208_ = lean_st_ref_get(v___y_3205_);
v_env_3212_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_ref(v_env_3212_);
lean_dec(v___x_3208_);
v___x_3227_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3212_, v_declName_3197_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_dec_ref(v_env_3212_);
lean_dec(v_declName_3197_);
goto v___jp_3209_;
}
else
{
lean_object* v_val_3228_; lean_object* v___x_3229_; lean_object* v_modules_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v_val_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_val_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___x_3229_ = l_Lean_Environment_header(v_env_3212_);
v_modules_3230_ = lean_ctor_get(v___x_3229_, 3);
lean_inc_ref(v_modules_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = lean_array_get_size(v_modules_3230_);
v___x_3232_ = lean_nat_dec_lt(v_val_3228_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_dec_ref(v_modules_3230_);
lean_dec(v_val_3228_);
lean_dec_ref(v_env_3212_);
lean_dec(v_declName_3197_);
goto v___jp_3209_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___y_3236_; 
v___x_3233_ = lean_array_fget(v_modules_3230_, v_val_3228_);
lean_dec(v_val_3228_);
lean_dec_ref(v_modules_3230_);
v___x_3234_ = lean_st_ref_get(v___y_3205_);
if (v_isMeta_3198_ == 0)
{
lean_dec(v___x_3234_);
v___y_3236_ = v_isMeta_3198_;
goto v___jp_3235_;
}
else
{
lean_object* v_env_3247_; uint8_t v___x_3248_; 
v_env_3247_ = lean_ctor_get(v___x_3234_, 0);
lean_inc_ref(v_env_3247_);
lean_dec(v___x_3234_);
lean_inc(v_declName_3197_);
v___x_3248_ = l_Lean_isMarkedMeta(v_env_3247_, v_declName_3197_);
if (v___x_3248_ == 0)
{
v___y_3236_ = v_isMeta_3198_;
goto v___jp_3235_;
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = 0;
v___y_3236_ = v___x_3249_;
goto v___jp_3235_;
}
}
v___jp_3235_:
{
lean_object* v_toImport_3237_; lean_object* v_module_3238_; lean_object* v___x_3239_; 
v_toImport_3237_ = lean_ctor_get(v___x_3233_, 0);
lean_inc_ref(v_toImport_3237_);
lean_dec(v___x_3233_);
v_module_3238_ = lean_ctor_get(v_toImport_3237_, 0);
lean_inc(v_module_3238_);
lean_dec_ref(v_toImport_3237_);
lean_inc(v_declName_3197_);
v___x_3239_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16(v_module_3238_, v___y_3236_, v_declName_3197_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_dec_ref_known(v___x_3239_, 1);
v___x_3240_ = l_Lean_indirectModUseExt;
v___x_3241_ = lean_box(1);
v___x_3242_ = lean_box(0);
lean_inc_ref(v_env_3212_);
v___x_3243_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3207_, v___x_3240_, v_env_3212_, v___x_3241_, v___x_3242_);
v___x_3244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v___x_3243_, v_declName_3197_);
lean_dec(v___x_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___closed__1));
v___y_3214_ = v___x_3245_;
goto v___jp_3213_;
}
else
{
lean_object* v_val_3246_; 
v_val_3246_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_val_3246_);
lean_dec_ref_known(v___x_3244_, 1);
v___y_3214_ = v_val_3246_;
goto v___jp_3213_;
}
}
else
{
lean_dec_ref(v_env_3212_);
lean_dec(v_declName_3197_);
return v___x_3239_;
}
}
}
}
v___jp_3209_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
v___jp_3213_:
{
lean_object* v___x_3215_; size_t v_sz_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3215_ = lean_box(0);
v_sz_3216_ = lean_array_size(v___y_3214_);
v___x_3217_ = ((size_t)0ULL);
v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__17(v_env_3212_, v_declName_3197_, v___y_3214_, v_sz_3216_, v___x_3217_, v___x_3215_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec_ref(v___y_3214_);
lean_dec_ref(v_env_3212_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v___x_3218_, 0);
lean_dec(v_unused_3226_);
v___x_3220_ = v___x_3218_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v___x_3218_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3215_);
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3215_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
else
{
return v___x_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12___boxed(lean_object* v_declName_3250_, lean_object* v_isMeta_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v_isMeta_boxed_3260_; lean_object* v_res_3261_; 
v_isMeta_boxed_3260_ = lean_unbox(v_isMeta_3251_);
v_res_3261_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_declName_3250_, v_isMeta_boxed_3260_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(lean_object* v_as_x27_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
if (lean_obj_tag(v_as_x27_3262_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_b_3263_);
return v___x_3272_;
}
else
{
lean_object* v_head_3273_; lean_object* v_tail_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v_head_3273_ = lean_ctor_get(v_as_x27_3262_, 0);
v_tail_3274_ = lean_ctor_get(v_as_x27_3262_, 1);
v___x_3275_ = lean_box(0);
v___x_3276_ = 1;
lean_inc(v_head_3273_);
v___x_3277_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12(v_head_3273_, v___x_3276_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref_known(v___x_3277_, 1);
v_as_x27_3262_ = v_tail_3274_;
v_b_3263_ = v___x_3275_;
goto _start;
}
else
{
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg___boxed(lean_object* v_as_x27_3279_, lean_object* v_b_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_3279_, v_b_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v_as_x27_3279_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(lean_object* v_currNamespace_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_currNamespace_3290_);
lean_ctor_set(v___x_3293_, 1, v___y_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed(lean_object* v_currNamespace_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3(v_currNamespace_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(lean_object* v_as_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
if (lean_obj_tag(v_as_3298_) == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
else
{
lean_object* v_toCold_3309_; lean_object* v_options_3310_; uint8_t v_hasTrace_3311_; 
v_toCold_3309_ = lean_ctor_get(v___y_3304_, 0);
v_options_3310_ = lean_ctor_get(v_toCold_3309_, 2);
v_hasTrace_3311_ = lean_ctor_get_uint8(v_options_3310_, sizeof(void*)*1);
if (v_hasTrace_3311_ == 0)
{
lean_object* v_tail_3312_; 
v_tail_3312_ = lean_ctor_get(v_as_3298_, 1);
lean_inc(v_tail_3312_);
lean_dec_ref_known(v_as_3298_, 2);
v_as_3298_ = v_tail_3312_;
goto _start;
}
else
{
lean_object* v_head_3314_; lean_object* v_tail_3315_; lean_object* v_fst_3316_; lean_object* v_snd_3317_; lean_object* v_inheritedTraceOptions_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_head_3314_ = lean_ctor_get(v_as_3298_, 0);
lean_inc(v_head_3314_);
v_tail_3315_ = lean_ctor_get(v_as_3298_, 1);
lean_inc(v_tail_3315_);
lean_dec_ref_known(v_as_3298_, 2);
v_fst_3316_ = lean_ctor_get(v_head_3314_, 0);
lean_inc_n(v_fst_3316_, 2);
v_snd_3317_ = lean_ctor_get(v_head_3314_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_head_3314_);
v_inheritedTraceOptions_3318_ = lean_ctor_get(v_toCold_3309_, 11);
v___x_3319_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3320_ = l_Lean_Name_append(v___x_3319_, v_fst_3316_);
v___x_3321_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3318_, v_options_3310_, v___x_3320_);
lean_dec(v___x_3320_);
if (v___x_3321_ == 0)
{
lean_dec(v_snd_3317_);
lean_dec(v_fst_3316_);
v_as_3298_ = v_tail_3315_;
goto _start;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_snd_3317_);
v___x_3324_ = l_Lean_MessageData_ofFormat(v___x_3323_);
v___x_3325_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_fst_3316_, v___x_3324_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_dec_ref_known(v___x_3325_, 1);
v_as_3298_ = v_tail_3315_;
goto _start;
}
else
{
lean_dec(v_tail_3315_);
return v___x_3325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14___boxed(lean_object* v_as_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v_as_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(lean_object* v_env_3337_, lean_object* v_declName_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v___x_3341_; lean_object* v_env_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; uint8_t v___x_3345_; 
v___x_3341_ = 0;
v_env_3342_ = l_Lean_Environment_setExporting(v_env_3337_, v___x_3341_);
lean_inc(v_declName_3338_);
v___x_3343_ = l_Lean_mkPrivateName(v_env_3342_, v_declName_3338_);
v___x_3344_ = 1;
lean_inc_ref(v_env_3342_);
v___x_3345_ = l_Lean_Environment_contains(v_env_3342_, v___x_3343_, v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3346_ = l_Lean_privateToUserName(v_declName_3338_);
v___x_3347_ = l_Lean_Environment_contains(v_env_3342_, v___x_3346_, v___x_3344_);
v___x_3348_ = lean_box(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v___y_3340_);
return v___x_3349_;
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v_env_3342_);
lean_dec(v_declName_3338_);
v___x_3350_ = lean_box(v___x_3345_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___y_3340_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed(lean_object* v_env_3352_, lean_object* v_declName_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1(v_env_3352_, v_declName_3353_, v___y_3354_, v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v_toCold_3368_; lean_object* v_env_3369_; lean_object* v_currRecDepth_3370_; lean_object* v_ref_3371_; lean_object* v_options_3372_; lean_object* v_maxRecDepth_3373_; lean_object* v_currNamespace_3374_; lean_object* v_openDecls_3375_; lean_object* v_quotContext_3376_; lean_object* v_currMacroScope_3377_; lean_object* v___f_3378_; lean_object* v___f_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v_methods_3383_; lean_object* v___x_3384_; lean_object* v_nextMacroScope_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3367_ = lean_st_ref_get(v___y_3365_);
v_toCold_3368_ = lean_ctor_get(v___y_3364_, 0);
v_env_3369_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref_n(v_env_3369_, 4);
lean_dec(v___x_3367_);
v_currRecDepth_3370_ = lean_ctor_get(v___y_3364_, 1);
v_ref_3371_ = lean_ctor_get(v___y_3364_, 2);
v_options_3372_ = lean_ctor_get(v_toCold_3368_, 2);
v_maxRecDepth_3373_ = lean_ctor_get(v_toCold_3368_, 3);
v_currNamespace_3374_ = lean_ctor_get(v_toCold_3368_, 4);
v_openDecls_3375_ = lean_ctor_get(v_toCold_3368_, 5);
v_quotContext_3376_ = lean_ctor_get(v_toCold_3368_, 8);
v_currMacroScope_3377_ = lean_ctor_get(v_toCold_3368_, 9);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3378_, 0, v_env_3369_);
v___f_3379_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3379_, 0, v_env_3369_);
lean_inc_n(v_openDecls_3375_, 2);
lean_inc_n(v_currNamespace_3374_, 3);
v___f_3380_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3380_, 0, v_env_3369_);
lean_closure_set(v___f_3380_, 1, v_currNamespace_3374_);
lean_closure_set(v___f_3380_, 2, v_openDecls_3375_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3381_, 0, v_currNamespace_3374_);
lean_inc_ref(v_options_3372_);
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_3382_, 0, v_env_3369_);
lean_closure_set(v___f_3382_, 1, v_options_3372_);
lean_closure_set(v___f_3382_, 2, v_currNamespace_3374_);
lean_closure_set(v___f_3382_, 3, v_openDecls_3375_);
v_methods_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_3383_, 0, v___f_3378_);
lean_ctor_set(v_methods_3383_, 1, v___f_3381_);
lean_ctor_set(v_methods_3383_, 2, v___f_3379_);
lean_ctor_set(v_methods_3383_, 3, v___f_3380_);
lean_ctor_set(v_methods_3383_, 4, v___f_3382_);
v___x_3384_ = lean_st_ref_get(v___y_3365_);
v_nextMacroScope_3385_ = lean_ctor_get(v___x_3384_, 1);
lean_inc(v_nextMacroScope_3385_);
lean_dec(v___x_3384_);
lean_inc(v_ref_3371_);
lean_inc(v_maxRecDepth_3373_);
lean_inc(v_currRecDepth_3370_);
lean_inc(v_currMacroScope_3377_);
lean_inc(v_quotContext_3376_);
v___x_3386_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3386_, 0, v_methods_3383_);
lean_ctor_set(v___x_3386_, 1, v_quotContext_3376_);
lean_ctor_set(v___x_3386_, 2, v_currMacroScope_3377_);
lean_ctor_set(v___x_3386_, 3, v_currRecDepth_3370_);
lean_ctor_set(v___x_3386_, 4, v_maxRecDepth_3373_);
lean_ctor_set(v___x_3386_, 5, v_ref_3371_);
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3388_, 0, v_nextMacroScope_3385_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
lean_ctor_set(v___x_3388_, 2, v___x_3387_);
v___x_3389_ = lean_apply_2(v_x_3358_, v___x_3386_, v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v_a_3391_; lean_object* v_macroScope_3392_; lean_object* v_traceMsgs_3393_; lean_object* v_expandedMacroDecls_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_a_3390_);
v_a_3391_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3389_, 2);
v_macroScope_3392_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_macroScope_3392_);
v_traceMsgs_3393_ = lean_ctor_get(v_a_3390_, 1);
lean_inc(v_traceMsgs_3393_);
v_expandedMacroDecls_3394_ = lean_ctor_get(v_a_3390_, 2);
lean_inc(v_expandedMacroDecls_3394_);
lean_dec(v_a_3390_);
v___x_3395_ = lean_box(0);
v___x_3396_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_expandedMacroDecls_3394_, v___x_3395_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v_expandedMacroDecls_3394_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; lean_object* v_env_3398_; lean_object* v_ngen_3399_; lean_object* v_auxDeclNGen_3400_; lean_object* v_traceState_3401_; lean_object* v_cache_3402_; lean_object* v_messages_3403_; lean_object* v_infoState_3404_; lean_object* v_snapshotTasks_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref_known(v___x_3396_, 1);
v___x_3397_ = lean_st_ref_take(v___y_3365_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
v_ngen_3399_ = lean_ctor_get(v___x_3397_, 2);
v_auxDeclNGen_3400_ = lean_ctor_get(v___x_3397_, 3);
v_traceState_3401_ = lean_ctor_get(v___x_3397_, 4);
v_cache_3402_ = lean_ctor_get(v___x_3397_, 5);
v_messages_3403_ = lean_ctor_get(v___x_3397_, 6);
v_infoState_3404_ = lean_ctor_get(v___x_3397_, 7);
v_snapshotTasks_3405_ = lean_ctor_get(v___x_3397_, 8);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v___x_3397_, 1);
lean_dec(v_unused_3432_);
v___x_3407_ = v___x_3397_;
v_isShared_3408_ = v_isSharedCheck_3431_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_snapshotTasks_3405_);
lean_inc(v_infoState_3404_);
lean_inc(v_messages_3403_);
lean_inc(v_cache_3402_);
lean_inc(v_traceState_3401_);
lean_inc(v_auxDeclNGen_3400_);
lean_inc(v_ngen_3399_);
lean_inc(v_env_3398_);
lean_dec(v___x_3397_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3431_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 1, v_macroScope_3392_);
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_env_3398_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_macroScope_3392_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_ngen_3399_);
lean_ctor_set(v_reuseFailAlloc_3430_, 3, v_auxDeclNGen_3400_);
lean_ctor_set(v_reuseFailAlloc_3430_, 4, v_traceState_3401_);
lean_ctor_set(v_reuseFailAlloc_3430_, 5, v_cache_3402_);
lean_ctor_set(v_reuseFailAlloc_3430_, 6, v_messages_3403_);
lean_ctor_set(v_reuseFailAlloc_3430_, 7, v_infoState_3404_);
lean_ctor_set(v_reuseFailAlloc_3430_, 8, v_snapshotTasks_3405_);
v___x_3410_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = lean_st_ref_put(v___y_3365_, v___x_3410_);
v___x_3412_ = l_List_reverse___redArg(v_traceMsgs_3393_);
v___x_3413_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__14(v___x_3412_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v___x_3413_, 0);
lean_dec(v_unused_3421_);
v___x_3415_ = v___x_3413_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v___x_3413_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_a_3391_);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3391_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_a_3391_);
v_a_3422_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3413_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3413_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v_traceMsgs_3393_);
lean_dec(v_macroScope_3392_);
lean_dec(v_a_3391_);
v_a_3433_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3396_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3396_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v_a_3441_; 
v_a_3441_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3389_, 2);
if (lean_obj_tag(v_a_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v_a_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v_a_3442_ = lean_ctor_get(v_a_3441_, 0);
lean_inc(v_a_3442_);
v_a_3443_ = lean_ctor_get(v_a_3441_, 1);
lean_inc_ref(v_a_3443_);
lean_dec_ref_known(v_a_3441_, 2);
v___x_3444_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___closed__0));
v___x_3445_ = lean_string_dec_eq(v_a_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_a_3443_);
v___x_3447_ = l_Lean_MessageData_ofFormat(v___x_3446_);
v___x_3448_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_a_3442_, v___x_3447_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v_a_3442_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; 
lean_dec_ref(v_a_3443_);
v___x_3449_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_a_3442_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg___boxed(lean_object* v_x_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(lean_object* v___x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_toCold_3465_; lean_object* v_quotContext_3466_; lean_object* v_currMacroScope_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_toCold_3465_ = lean_ctor_get(v___y_3462_, 0);
lean_inc_ref(v_toCold_3465_);
lean_dec_ref(v___y_3462_);
v_quotContext_3466_ = lean_ctor_get(v_toCold_3465_, 8);
lean_inc(v_quotContext_3466_);
v_currMacroScope_3467_ = lean_ctor_get(v_toCold_3465_, 9);
lean_inc(v_currMacroScope_3467_);
lean_dec_ref(v_toCold_3465_);
v___x_3468_ = l_Lean_addMacroScope(v_quotContext_3466_, v___x_3461_, v_currMacroScope_3467_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v___x_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___lam__0(v___x_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___f_3483_; lean_object* v___x_3484_; 
v___f_3483_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___closed__2));
v___x_3484_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_3483_, v___y_3480_, v___y_3481_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg___boxed(lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(lean_object* v_ref_3489_, uint8_t v_canonical_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3496_, v___y_3497_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3508_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3504_ = l_Lean_mkIdentFrom(v_ref_3489_, v_a_3500_, v_canonical_3490_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3504_);
v___x_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
v_a_3509_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3499_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3499_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6___boxed(lean_object* v_ref_3517_, lean_object* v_canonical_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v_canonical_boxed_3527_; lean_object* v_res_3528_; 
v_canonical_boxed_3527_ = lean_unbox(v_canonical_3518_);
v_res_3528_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_ref_3517_, v_canonical_boxed_3527_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v_ref_3517_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__0));
v___x_3531_ = l_Lean_stringToMessageData(v___x_3530_);
return v___x_3531_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3538_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16___closed__13));
v___x_3539_ = l_Lean_Name_append(v___x_3538_, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__5));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__7));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign___boxed(lean_object* v_config_3552_, lean_object* v_letOrReassign_3553_, lean_object* v_decl_3554_, lean_object* v_tk_3555_, lean_object* v_dec_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_config_3552_, v_letOrReassign_3553_, v_decl_3554_, v_tk_3555_, v_dec_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetOrReassign(lean_object* v_config_3566_, lean_object* v_letOrReassign_3567_, lean_object* v_decl_3568_, lean_object* v_tk_3569_, lean_object* v_dec_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_config_3566_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3580_; 
lean_dec_ref_known(v___x_3579_, 1);
lean_inc(v_decl_3568_);
v___x_3580_ = l_Lean_Elab_Do_getLetDeclVars(v_decl_3568_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3582_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v_letOrReassign_3567_, v_a_3581_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; 
lean_dec_ref_known(v___x_3582_, 1);
v___x_3583_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3570_, v_tk_3569_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v_rhs_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v_xType_x3f_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; uint8_t v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; uint8_t v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; uint8_t v___y_3690_; uint8_t v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; uint8_t v___y_3701_; uint8_t v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; uint8_t v___y_3766_; uint8_t v___y_3767_; lean_object* v_id_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; uint8_t v___y_3787_; lean_object* v___y_3788_; uint8_t v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; uint8_t v___y_3793_; lean_object* v___y_3794_; uint8_t v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v_decl_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___x_3886_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3583_, 1);
v___x_3886_ = l_Lean_Elab_Do_isErased___redArg(v_letOrReassign_3567_, v_a_3581_, v_a_3571_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment(v_letOrReassign_3567_, v_decl_3568_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3888_) == 0)
{
uint8_t v___x_3889_; 
v___x_3889_ = lean_unbox(v_a_3887_);
lean_dec(v_a_3887_);
if (v___x_3889_ == 0)
{
lean_object* v_a_3890_; 
v_a_3890_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3888_, 1);
v_decl_3817_ = v_a_3890_;
v___y_3818_ = v_a_3571_;
v___y_3819_ = v_a_3572_;
v___y_3820_ = v_a_3573_;
v___y_3821_ = v_a_3574_;
v___y_3822_ = v_a_3575_;
v___y_3823_ = v_a_3576_;
v___y_3824_ = v_a_3577_;
goto v___jp_3816_;
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3892_; 
v_a_3891_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3892_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl(v_a_3891_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v_decl_3817_ = v_a_3893_;
v___y_3818_ = v_a_3571_;
v___y_3819_ = v_a_3572_;
v___y_3820_ = v_a_3573_;
v___y_3821_ = v_a_3574_;
v___y_3822_ = v_a_3575_;
v___y_3823_ = v_a_3576_;
v___y_3824_ = v_a_3577_;
goto v___jp_3816_;
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3894_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3892_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3892_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_a_3887_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3902_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3888_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3888_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_decl_3568_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3910_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3886_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3886_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
v___jp_3585_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3603_ = lean_box(v___y_3590_);
v___x_3604_ = lean_box(v___y_3586_);
lean_inc_ref(v___y_3592_);
lean_inc_ref(v___y_3588_);
lean_inc_ref(v___y_3593_);
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___boxed), 19, 10);
lean_closure_set(v___f_3605_, 0, v_rhs_3595_);
lean_closure_set(v___f_3605_, 1, v___x_3603_);
lean_closure_set(v___f_3605_, 2, v_config_3566_);
lean_closure_set(v___f_3605_, 3, v___y_3591_);
lean_closure_set(v___f_3605_, 4, v___x_3604_);
lean_closure_set(v___f_3605_, 5, v___y_3593_);
lean_closure_set(v___f_3605_, 6, v___y_3588_);
lean_closure_set(v___f_3605_, 7, v___y_3592_);
lean_closure_set(v___f_3605_, 8, v___y_3589_);
lean_closure_set(v___f_3605_, 9, v___y_3587_);
v___x_3606_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_3606_, 0, v_a_3584_);
v___x_3607_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabWithReassignments___boxed), 11, 3);
lean_closure_set(v___x_3607_, 0, v_letOrReassign_3567_);
lean_closure_set(v___x_3607_, 1, v_a_3581_);
lean_closure_set(v___x_3607_, 2, v___x_3606_);
v___x_3608_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__1, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__1);
v___x_3609_ = l_Lean_MessageData_ofSyntax(v___y_3594_);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_box(0);
v___x_3612_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_3610_, v___x_3607_, v___f_3605_, v___x_3611_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3612_;
}
v___jp_3613_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_unsigned_to_nat(4u);
v___x_3636_ = l_Lean_Syntax_getArg(v___y_3625_, v___x_3635_);
lean_dec(v___y_3625_);
if (lean_obj_tag(v_xType_x3f_3627_) == 0)
{
lean_inc(v___y_3615_);
v___y_3586_ = v___y_3614_;
v___y_3587_ = v___y_3615_;
v___y_3588_ = v___y_3616_;
v___y_3589_ = v___y_3618_;
v___y_3590_ = v___y_3617_;
v___y_3591_ = v___y_3619_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v___y_3615_;
v_rhs_3595_ = v___x_3636_;
v___y_3596_ = v___y_3628_;
v___y_3597_ = v___y_3629_;
v___y_3598_ = v___y_3630_;
v___y_3599_ = v___y_3631_;
v___y_3600_ = v___y_3632_;
v___y_3601_ = v___y_3633_;
v___y_3602_ = v___y_3634_;
goto v___jp_3585_;
}
else
{
lean_object* v_toCold_3637_; lean_object* v_val_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3681_; 
v_toCold_3637_ = lean_ctor_get(v___y_3633_, 0);
v_val_3638_ = lean_ctor_get(v_xType_x3f_3627_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_xType_x3f_3627_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3640_ = v_xType_x3f_3627_;
v_isShared_3641_ = v_isSharedCheck_3681_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_val_3638_);
lean_dec(v_xType_x3f_3627_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3681_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_ref_3642_; lean_object* v_quotContext_3643_; lean_object* v_currMacroScope_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v_ref_3642_ = lean_ctor_get(v___y_3633_, 2);
v_quotContext_3643_ = lean_ctor_get(v_toCold_3637_, 8);
v_currMacroScope_3644_ = lean_ctor_get(v_toCold_3637_, 9);
v___x_3645_ = l_Lean_SourceInfo_fromRef(v_ref_3642_, v___y_3623_);
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__15));
lean_inc_ref_n(v___y_3624_, 2);
lean_inc_ref_n(v___y_3622_, 2);
lean_inc_ref_n(v___y_3626_, 3);
v___x_3647_ = l_Lean_Name_mkStr4(v___y_3626_, v___y_3622_, v___y_3624_, v___x_3646_);
v___x_3648_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__17));
v___x_3649_ = l_Lean_Name_mkStr4(v___y_3626_, v___y_3622_, v___y_3624_, v___x_3648_);
v___x_3650_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__19));
lean_inc(v___x_3645_);
v___x_3651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3645_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__21));
v___x_3653_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__23);
v___x_3654_ = lean_box(0);
lean_inc(v_currMacroScope_3644_);
lean_inc(v_quotContext_3643_);
v___x_3655_ = l_Lean_addMacroScope(v_quotContext_3643_, v___x_3654_, v_currMacroScope_3644_);
v___x_3656_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__24));
v___x_3657_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__25));
v___x_3658_ = l_Lean_Name_mkStr3(v___y_3626_, v___x_3656_, v___x_3657_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3658_);
v___x_3660_ = v___x_3640_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__28));
lean_inc_ref_n(v___y_3626_, 2);
v___x_3662_ = l_Lean_Name_mkStr2(v___y_3626_, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_inc_ref(v___y_3624_);
lean_inc_ref(v___y_3622_);
v___x_3664_ = l_Lean_Name_mkStr3(v___y_3626_, v___y_3622_, v___y_3624_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3663_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3660_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
lean_inc_n(v___x_3645_, 6);
v___x_3670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3645_);
lean_ctor_set(v___x_3670_, 1, v___x_3653_);
lean_ctor_set(v___x_3670_, 2, v___x_3655_);
lean_ctor_set(v___x_3670_, 3, v___x_3669_);
v___x_3671_ = l_Lean_Syntax_node1(v___x_3645_, v___x_3652_, v___x_3670_);
v___x_3672_ = l_Lean_Syntax_node2(v___x_3645_, v___x_3649_, v___x_3651_, v___x_3671_);
v___x_3673_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_3674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3645_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_3676_ = l_Lean_Syntax_node1(v___x_3645_, v___x_3675_, v_val_3638_);
v___x_3677_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__37));
v___x_3678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3645_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_Syntax_node5(v___x_3645_, v___x_3647_, v___x_3672_, v___x_3636_, v___x_3674_, v___x_3676_, v___x_3678_);
lean_inc(v___y_3615_);
v___y_3586_ = v___y_3614_;
v___y_3587_ = v___y_3615_;
v___y_3588_ = v___y_3616_;
v___y_3589_ = v___y_3618_;
v___y_3590_ = v___y_3617_;
v___y_3591_ = v___y_3619_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v___y_3615_;
v_rhs_3595_ = v___x_3679_;
v___y_3596_ = v___y_3628_;
v___y_3597_ = v___y_3629_;
v___y_3598_ = v___y_3630_;
v___y_3599_ = v___y_3631_;
v___y_3600_ = v___y_3632_;
v___y_3601_ = v___y_3633_;
v___y_3602_ = v___y_3634_;
goto v___jp_3585_;
}
}
}
}
v___jp_3682_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; 
v___x_3702_ = lean_box(v___y_3683_);
v___x_3703_ = lean_box(v___y_3690_);
v___x_3704_ = lean_box(v___y_3701_);
v___f_3705_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3705_, 0, v___y_3686_);
lean_closure_set(v___f_3705_, 1, v___y_3689_);
lean_closure_set(v___f_3705_, 2, v___x_3702_);
lean_closure_set(v___f_3705_, 3, v___x_3703_);
lean_closure_set(v___f_3705_, 4, v___y_3684_);
lean_closure_set(v___f_3705_, 5, v___x_3704_);
v___x_3706_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___y_3697_, v___f_3705_, v___y_3695_, v___y_3696_, v___y_3694_, v___y_3698_, v___y_3699_, v___y_3692_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v_toCold_3708_; lean_object* v_options_3709_; lean_object* v_fst_3710_; lean_object* v_snd_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3750_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v_toCold_3708_ = lean_ctor_get(v___y_3699_, 0);
v_options_3709_ = lean_ctor_get(v_toCold_3708_, 2);
v_fst_3710_ = lean_ctor_get(v_a_3707_, 0);
v_snd_3711_ = lean_ctor_get(v_a_3707_, 1);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_a_3707_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3713_ = v_a_3707_;
v_isShared_3714_ = v_isSharedCheck_3750_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_snd_3711_);
lean_inc(v_fst_3710_);
lean_dec(v_a_3707_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3750_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_inheritedTraceOptions_3715_; uint8_t v_hasTrace_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_inheritedTraceOptions_3715_ = lean_ctor_get(v_toCold_3708_, 11);
v_hasTrace_3716_ = lean_ctor_get_uint8(v_options_3709_, sizeof(void*)*1);
v___x_3717_ = lean_box(v___y_3687_);
v___x_3718_ = lean_box(v___y_3691_);
v___x_3719_ = lean_box(v___y_3701_);
v___x_3720_ = lean_box(v___y_3683_);
lean_inc(v_snd_3711_);
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__3___boxed), 19, 10);
lean_closure_set(v___f_3721_, 0, v___y_3685_);
lean_closure_set(v___f_3721_, 1, v___y_3688_);
lean_closure_set(v___f_3721_, 2, v_a_3584_);
lean_closure_set(v___f_3721_, 3, v_letOrReassign_3567_);
lean_closure_set(v___f_3721_, 4, v_a_3581_);
lean_closure_set(v___f_3721_, 5, v___x_3717_);
lean_closure_set(v___f_3721_, 6, v___x_3718_);
lean_closure_set(v___f_3721_, 7, v_snd_3711_);
lean_closure_set(v___f_3721_, 8, v___x_3719_);
lean_closure_set(v___f_3721_, 9, v___x_3720_);
v___x_3722_ = l_Lean_Syntax_getId(v___y_3693_);
lean_dec(v___y_3693_);
v___x_3723_ = l_Lean_LocalDeclKind_ofBinderName(v___x_3722_);
if (v_hasTrace_3716_ == 0)
{
lean_object* v___x_3724_; 
lean_del_object(v___x_3713_);
v___x_3724_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3722_, v_fst_3710_, v_snd_3711_, v___f_3721_, v___y_3701_, v___x_3723_, v___y_3700_, v___y_3695_, v___y_3696_, v___y_3694_, v___y_3698_, v___y_3699_, v___y_3692_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__3));
v___x_3726_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__4, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__4_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__4);
v___x_3727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3715_, v_options_3709_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; 
lean_del_object(v___x_3713_);
v___x_3728_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3722_, v_fst_3710_, v_snd_3711_, v___f_3721_, v___y_3701_, v___x_3723_, v___y_3700_, v___y_3695_, v___y_3696_, v___y_3694_, v___y_3698_, v___y_3699_, v___y_3692_);
return v___x_3728_;
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3732_; 
lean_inc(v___x_3722_);
v___x_3729_ = l_Lean_MessageData_ofName(v___x_3722_);
v___x_3730_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__6, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__6_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__6);
if (v_isShared_3714_ == 0)
{
lean_ctor_set_tag(v___x_3713_, 7);
lean_ctor_set(v___x_3713_, 1, v___x_3730_);
lean_ctor_set(v___x_3713_, 0, v___x_3729_);
v___x_3732_ = v___x_3713_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_inc(v_fst_3710_);
v___x_3733_ = l_Lean_MessageData_ofExpr(v_fst_3710_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetOrReassign___closed__8, &l_Lean_Elab_Do_elabDoLetOrReassign___closed__8_once, _init_l_Lean_Elab_Do_elabDoLetOrReassign___closed__8);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
lean_inc(v_snd_3711_);
v___x_3737_ = l_Lean_MessageData_ofExpr(v_snd_3711_);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v___x_3725_, v___x_3738_, v___y_3694_, v___y_3698_, v___y_3699_, v___y_3692_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; 
lean_dec_ref_known(v___x_3739_, 1);
v___x_3740_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__4___redArg(v___x_3722_, v_fst_3710_, v_snd_3711_, v___f_3721_, v___y_3701_, v___x_3723_, v___y_3700_, v___y_3695_, v___y_3696_, v___y_3694_, v___y_3698_, v___y_3699_, v___y_3692_);
return v___x_3740_;
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v___x_3722_);
lean_dec_ref(v___f_3721_);
lean_dec(v_snd_3711_);
lean_dec(v_fst_3710_);
v_a_3741_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3739_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3739_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
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
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v___y_3693_);
lean_dec(v___y_3688_);
lean_dec(v___y_3685_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
v_a_3751_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3706_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3706_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
v___jp_3759_:
{
uint8_t v_nondep_3776_; 
v_nondep_3776_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1);
if (v_nondep_3776_ == 0)
{
if (lean_obj_tag(v_letOrReassign_3567_) == 1)
{
uint8_t v_usedOnly_3777_; uint8_t v_zeta_3778_; lean_object* v_eq_x3f_3779_; 
v_usedOnly_3777_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 1);
v_zeta_3778_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 2);
v_eq_x3f_3779_ = lean_ctor_get(v_config_3566_, 0);
lean_inc(v_eq_x3f_3779_);
lean_dec_ref(v_config_3566_);
lean_inc(v_id_3768_);
v___y_3683_ = v___y_3760_;
v___y_3684_ = v___y_3761_;
v___y_3685_ = v_id_3768_;
v___y_3686_ = v___y_3762_;
v___y_3687_ = v_zeta_3778_;
v___y_3688_ = v_eq_x3f_3779_;
v___y_3689_ = v___y_3764_;
v___y_3690_ = v___y_3765_;
v___y_3691_ = v_usedOnly_3777_;
v___y_3692_ = v___y_3775_;
v___y_3693_ = v_id_3768_;
v___y_3694_ = v___y_3772_;
v___y_3695_ = v___y_3770_;
v___y_3696_ = v___y_3771_;
v___y_3697_ = v___y_3763_;
v___y_3698_ = v___y_3773_;
v___y_3699_ = v___y_3774_;
v___y_3700_ = v___y_3769_;
v___y_3701_ = v___y_3766_;
goto v___jp_3682_;
}
else
{
uint8_t v_usedOnly_3780_; uint8_t v_zeta_3781_; lean_object* v_eq_x3f_3782_; 
v_usedOnly_3780_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 1);
v_zeta_3781_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 2);
v_eq_x3f_3782_ = lean_ctor_get(v_config_3566_, 0);
lean_inc(v_eq_x3f_3782_);
lean_dec_ref(v_config_3566_);
lean_inc(v_id_3768_);
v___y_3683_ = v___y_3760_;
v___y_3684_ = v___y_3761_;
v___y_3685_ = v_id_3768_;
v___y_3686_ = v___y_3762_;
v___y_3687_ = v_zeta_3781_;
v___y_3688_ = v_eq_x3f_3782_;
v___y_3689_ = v___y_3764_;
v___y_3690_ = v___y_3765_;
v___y_3691_ = v_usedOnly_3780_;
v___y_3692_ = v___y_3775_;
v___y_3693_ = v_id_3768_;
v___y_3694_ = v___y_3772_;
v___y_3695_ = v___y_3770_;
v___y_3696_ = v___y_3771_;
v___y_3697_ = v___y_3763_;
v___y_3698_ = v___y_3773_;
v___y_3699_ = v___y_3774_;
v___y_3700_ = v___y_3769_;
v___y_3701_ = v___y_3767_;
goto v___jp_3682_;
}
}
else
{
uint8_t v_usedOnly_3783_; uint8_t v_zeta_3784_; lean_object* v_eq_x3f_3785_; 
v_usedOnly_3783_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 1);
v_zeta_3784_ = lean_ctor_get_uint8(v_config_3566_, sizeof(void*)*1 + 2);
v_eq_x3f_3785_ = lean_ctor_get(v_config_3566_, 0);
lean_inc(v_eq_x3f_3785_);
lean_dec_ref(v_config_3566_);
lean_inc(v_id_3768_);
v___y_3683_ = v___y_3760_;
v___y_3684_ = v___y_3761_;
v___y_3685_ = v_id_3768_;
v___y_3686_ = v___y_3762_;
v___y_3687_ = v_zeta_3784_;
v___y_3688_ = v_eq_x3f_3785_;
v___y_3689_ = v___y_3764_;
v___y_3690_ = v___y_3765_;
v___y_3691_ = v_usedOnly_3783_;
v___y_3692_ = v___y_3775_;
v___y_3693_ = v_id_3768_;
v___y_3694_ = v___y_3772_;
v___y_3695_ = v___y_3770_;
v___y_3696_ = v___y_3771_;
v___y_3697_ = v___y_3763_;
v___y_3698_ = v___y_3773_;
v___y_3699_ = v___y_3774_;
v___y_3700_ = v___y_3769_;
v___y_3701_ = v___y_3766_;
goto v___jp_3682_;
}
}
v___jp_3786_:
{
lean_object* v___x_3800_; lean_object* v_id_3801_; lean_object* v_binders_3802_; lean_object* v_type_3803_; lean_object* v_value_3804_; uint8_t v___x_3805_; 
v___x_3800_ = l_Lean_Elab_Term_mkLetIdDeclView(v___y_3796_);
lean_dec(v___y_3796_);
v_id_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_id_3801_);
v_binders_3802_ = lean_ctor_get(v___x_3800_, 1);
lean_inc_ref(v_binders_3802_);
v_type_3803_ = lean_ctor_get(v___x_3800_, 2);
lean_inc(v_type_3803_);
v_value_3804_ = lean_ctor_get(v___x_3800_, 3);
lean_inc(v_value_3804_);
lean_dec_ref(v___x_3800_);
v___x_3805_ = l_Lean_Syntax_isIdent(v_id_3801_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6(v_id_3801_, v___y_3793_, v___y_3794_, v___y_3792_, v___y_3799_, v___y_3791_, v___y_3798_, v___y_3797_, v___y_3790_);
lean_dec(v_id_3801_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___y_3760_ = v___y_3787_;
v___y_3761_ = v___y_3788_;
v___y_3762_ = v_type_3803_;
v___y_3763_ = v_binders_3802_;
v___y_3764_ = v_value_3804_;
v___y_3765_ = v___y_3789_;
v___y_3766_ = v___y_3793_;
v___y_3767_ = v___y_3795_;
v_id_3768_ = v_a_3807_;
v___y_3769_ = v___y_3794_;
v___y_3770_ = v___y_3792_;
v___y_3771_ = v___y_3799_;
v___y_3772_ = v___y_3791_;
v___y_3773_ = v___y_3798_;
v___y_3774_ = v___y_3797_;
v___y_3775_ = v___y_3790_;
goto v___jp_3759_;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_value_3804_);
lean_dec(v_type_3803_);
lean_dec_ref(v_binders_3802_);
lean_dec(v___y_3788_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3808_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3806_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
v___y_3760_ = v___y_3787_;
v___y_3761_ = v___y_3788_;
v___y_3762_ = v_type_3803_;
v___y_3763_ = v_binders_3802_;
v___y_3764_ = v_value_3804_;
v___y_3765_ = v___y_3789_;
v___y_3766_ = v___y_3793_;
v___y_3767_ = v___y_3795_;
v_id_3768_ = v_id_3801_;
v___y_3769_ = v___y_3794_;
v___y_3770_ = v___y_3792_;
v___y_3771_ = v___y_3799_;
v___y_3772_ = v___y_3791_;
v___y_3773_ = v___y_3798_;
v___y_3774_ = v___y_3797_;
v___y_3775_ = v___y_3790_;
goto v___jp_3759_;
}
}
v___jp_3816_:
{
lean_object* v_doBlockResultType_3825_; lean_object* v___x_3826_; 
v_doBlockResultType_3825_ = lean_ctor_get(v___y_3818_, 3);
lean_inc_ref(v_doBlockResultType_3825_);
v___x_3826_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3825_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3885_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3829_ = v___x_3826_;
v_isShared_3830_ = v_isSharedCheck_3885_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3885_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v___x_3831_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_3832_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_3833_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_3817_);
v___x_3835_ = l_Lean_Syntax_isOfKind(v_decl_3817_, v___x_3834_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
lean_dec(v_decl_3817_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v___x_3836_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3836_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = l_Lean_Syntax_getArg(v_decl_3817_, v___x_3837_);
lean_dec(v_decl_3817_);
v___x_3839_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___closed__10));
lean_inc(v___x_3838_);
v___x_3840_ = l_Lean_Syntax_isOfKind(v___x_3838_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; uint8_t v___x_3842_; 
lean_dec(v_tk_3569_);
v___x_3841_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_3838_);
v___x_3842_ = l_Lean_Syntax_isOfKind(v___x_3838_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3843_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___x_3838_);
v___x_3844_ = l_Lean_Syntax_isOfKind(v___x_3838_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
lean_dec(v___x_3838_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v___x_3845_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3845_;
}
else
{
v___y_3787_ = v___x_3835_;
v___y_3788_ = v___x_3837_;
v___y_3789_ = v___x_3842_;
v___y_3790_ = v___y_3824_;
v___y_3791_ = v___y_3821_;
v___y_3792_ = v___y_3819_;
v___y_3793_ = v___x_3835_;
v___y_3794_ = v___y_3818_;
v___y_3795_ = v___x_3842_;
v___y_3796_ = v___x_3838_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3820_;
goto v___jp_3786_;
}
}
else
{
v___y_3787_ = v___x_3835_;
v___y_3788_ = v___x_3837_;
v___y_3789_ = v___x_3842_;
v___y_3790_ = v___y_3824_;
v___y_3791_ = v___y_3821_;
v___y_3792_ = v___y_3819_;
v___y_3793_ = v___x_3835_;
v___y_3794_ = v___y_3818_;
v___y_3795_ = v___x_3842_;
v___y_3796_ = v___x_3838_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3820_;
goto v___jp_3786_;
}
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = l_Lean_Syntax_getArg(v___x_3838_, v___x_3846_);
v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3847_, v___x_3837_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec(v___x_3838_);
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v___x_3849_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3849_;
}
else
{
lean_object* v___x_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3850_ = lean_box(v___x_3840_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__4___boxed), 10, 1);
lean_closure_set(v___f_3851_, 0, v___x_3850_);
v___x_3852_ = l_Lean_Syntax_getArg(v___x_3838_, v___x_3837_);
v___x_3853_ = lean_unsigned_to_nat(2u);
v___x_3854_ = l_Lean_Syntax_getArg(v___x_3838_, v___x_3853_);
v___x_3855_ = l_Lean_Syntax_isNone(v___x_3854_);
if (v___x_3855_ == 0)
{
uint8_t v___x_3856_; 
lean_inc(v___x_3854_);
v___x_3856_ = l_Lean_Syntax_matchesNull(v___x_3854_, v___x_3846_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec(v___x_3854_);
lean_dec(v___x_3852_);
lean_dec_ref(v___f_3851_);
lean_dec(v___x_3838_);
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v___x_3857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3858_ = l_Lean_Syntax_getArg(v___x_3854_, v___x_3837_);
lean_dec(v___x_3854_);
v___x_3859_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_3858_);
v___x_3860_ = l_Lean_Syntax_isOfKind(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v___x_3858_);
lean_dec(v___x_3852_);
lean_dec_ref(v___f_3851_);
lean_dec(v___x_3838_);
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v___x_3861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3862_ = l_Lean_Syntax_getArg(v___x_3858_, v___x_3846_);
lean_dec(v___x_3858_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 1);
lean_ctor_set(v___x_3829_, 0, v___x_3862_);
v___x_3864_ = v___x_3829_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
v___y_3614_ = v___x_3835_;
v___y_3615_ = v___x_3852_;
v___y_3616_ = v___x_3832_;
v___y_3617_ = v___x_3840_;
v___y_3618_ = v___f_3851_;
v___y_3619_ = v_a_3827_;
v___y_3620_ = v___x_3833_;
v___y_3621_ = v___x_3831_;
v___y_3622_ = v___x_3832_;
v___y_3623_ = v___x_3840_;
v___y_3624_ = v___x_3833_;
v___y_3625_ = v___x_3838_;
v___y_3626_ = v___x_3831_;
v_xType_x3f_3627_ = v___x_3864_;
v___y_3628_ = v___y_3818_;
v___y_3629_ = v___y_3819_;
v___y_3630_ = v___y_3820_;
v___y_3631_ = v___y_3821_;
v___y_3632_ = v___y_3822_;
v___y_3633_ = v___y_3823_;
v___y_3634_ = v___y_3824_;
goto v___jp_3613_;
}
}
}
}
else
{
lean_object* v___x_3866_; 
lean_dec(v___x_3854_);
lean_del_object(v___x_3829_);
v___x_3866_ = lean_box(0);
v___y_3614_ = v___x_3835_;
v___y_3615_ = v___x_3852_;
v___y_3616_ = v___x_3832_;
v___y_3617_ = v___x_3840_;
v___y_3618_ = v___f_3851_;
v___y_3619_ = v_a_3827_;
v___y_3620_ = v___x_3833_;
v___y_3621_ = v___x_3831_;
v___y_3622_ = v___x_3832_;
v___y_3623_ = v___x_3840_;
v___y_3624_ = v___x_3833_;
v___y_3625_ = v___x_3838_;
v___y_3626_ = v___x_3831_;
v_xType_x3f_3627_ = v___x_3866_;
v___y_3628_ = v___y_3818_;
v___y_3629_ = v___y_3819_;
v___y_3630_ = v___y_3820_;
v___y_3631_ = v___y_3821_;
v___y_3632_ = v___y_3822_;
v___y_3633_ = v___y_3823_;
v___y_3634_ = v___y_3824_;
goto v___jp_3613_;
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_del_object(v___x_3829_);
lean_dec(v_a_3827_);
lean_dec(v_a_3581_);
v___x_3867_ = lean_box(v___x_3835_);
lean_inc(v___x_3838_);
v___x_3868_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandLetEqnsDecl___boxed), 4, 2);
lean_closure_set(v___x_3868_, 0, v___x_3838_);
lean_closure_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v___x_3868_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v_ref_3871_; uint8_t v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v_ref_3871_ = lean_ctor_get(v___y_3823_, 2);
v___x_3872_ = 0;
v___x_3873_ = l_Lean_SourceInfo_fromRef(v_ref_3871_, v___x_3872_);
v___x_3874_ = l_Lean_Syntax_node1(v___x_3873_, v___x_3834_, v_a_3870_);
lean_inc(v___x_3874_);
v___x_3875_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetOrReassign___boxed), 13, 5);
lean_closure_set(v___x_3875_, 0, v_config_3566_);
lean_closure_set(v___x_3875_, 1, v_letOrReassign_3567_);
lean_closure_set(v___x_3875_, 2, v___x_3874_);
lean_closure_set(v___x_3875_, 3, v_tk_3569_);
lean_closure_set(v___x_3875_, 4, v_a_3584_);
v___x_3876_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v___x_3838_, v___x_3874_, v___x_3875_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v___x_3838_);
lean_dec(v_a_3584_);
lean_dec(v_tk_3569_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3877_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3869_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3869_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
}
else
{
lean_dec(v_decl_3817_);
lean_dec(v_a_3584_);
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
return v___x_3826_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_a_3581_);
lean_dec(v_tk_3569_);
lean_dec(v_decl_3568_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3918_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3583_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3583_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3581_);
lean_dec_ref(v_dec_3570_);
lean_dec(v_tk_3569_);
lean_dec(v_decl_3568_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3926_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3582_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3582_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v_dec_3570_);
lean_dec(v_tk_3569_);
lean_dec(v_decl_3568_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3934_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3580_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3580_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec_ref(v_dec_3570_);
lean_dec(v_tk_3569_);
lean_dec(v_decl_3568_);
lean_dec(v_letOrReassign_3567_);
lean_dec_ref(v_config_3566_);
v_a_3942_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3579_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3579_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0(lean_object* v_00_u03b2_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0___redArg(v_x_3951_, v_x_3952_, v_x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(lean_object* v_cls_3955_, lean_object* v_msg_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___redArg(v_cls_3955_, v_msg_3956_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5___boxed(lean_object* v_cls_3966_, lean_object* v_msg_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_addTrace___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__5(v_cls_3966_, v_msg_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v___y_3968_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; 
v___x_3985_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___redArg(v___y_3982_, v___y_3983_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7___boxed(lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__6_spec__7(v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(lean_object* v_00_u03b1_3995_, lean_object* v_beforeStx_3996_, lean_object* v_afterStx_3997_, lean_object* v_x_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___redArg(v_beforeStx_3996_, v_afterStx_3997_, v_x_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7___boxed(lean_object* v_00_u03b1_4008_, lean_object* v_beforeStx_4009_, lean_object* v_afterStx_4010_, lean_object* v_x_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7(v_00_u03b1_4008_, v_beforeStx_4009_, v_afterStx_4010_, v_x_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v___y_4012_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(lean_object* v_00_u03b1_4021_, lean_object* v_x_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___redArg(v_x_4022_, v___y_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11___boxed(lean_object* v_00_u03b1_4026_, lean_object* v_x_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__11(v_00_u03b1_4026_, v_x_4027_, v___y_4028_, v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec_ref(v_x_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(lean_object* v_00_u03b1_4031_, lean_object* v_ref_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___redArg(v_ref_4032_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15___boxed(lean_object* v_00_u03b1_4042_, lean_object* v_ref_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__15(v_00_u03b1_4042_, v_ref_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(lean_object* v_00_u03b1_4053_, lean_object* v_x_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___redArg(v_x_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_x_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8(v_00_u03b1_4064_, v_x_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(lean_object* v_00_u03b2_4075_, lean_object* v_x_4076_, size_t v_x_4077_, size_t v_x_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___redArg(v_x_4076_, v_x_4077_, v_x_4078_, v_x_4079_, v_x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_, lean_object* v_x_4085_, lean_object* v_x_4086_, lean_object* v_x_4087_){
_start:
{
size_t v_x_92273__boxed_4088_; size_t v_x_92274__boxed_4089_; lean_object* v_res_4090_; 
v_x_92273__boxed_4088_ = lean_unbox_usize(v_x_4084_);
lean_dec(v_x_4084_);
v_x_92274__boxed_4089_ = lean_unbox_usize(v_x_4085_);
lean_dec(v_x_4085_);
v_res_4090_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0(v_00_u03b2_4082_, v_x_4083_, v_x_92273__boxed_4088_, v_x_92274__boxed_4089_, v_x_4086_, v_x_4087_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(lean_object* v_00_u03b1_4091_, lean_object* v_stx_4092_, lean_object* v_output_4093_, lean_object* v_x_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___redArg(v_stx_4092_, v_output_4093_, v_x_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_stx_4104_, lean_object* v_output_4105_, lean_object* v_x_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9(v_00_u03b1_4103_, v_stx_4104_, v_output_4105_, v_x_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(lean_object* v_as_4115_, lean_object* v_as_x27_4116_, lean_object* v_b_4117_, lean_object* v_a_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___redArg(v_as_x27_4116_, v_b_4117_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13___boxed(lean_object* v_as_4128_, lean_object* v_as_x27_4129_, lean_object* v_b_4130_, lean_object* v_a_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__13(v_as_4128_, v_as_x27_4129_, v_b_4130_, v_a_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v_as_x27_4129_);
lean_dec(v_as_4128_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_4141_, lean_object* v_n_4142_, lean_object* v_k_4143_, lean_object* v_v_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3___redArg(v_n_4142_, v_k_4143_, v_v_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_4146_, size_t v_depth_4147_, lean_object* v_keys_4148_, lean_object* v_vals_4149_, lean_object* v_heq_4150_, lean_object* v_i_4151_, lean_object* v_entries_4152_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___redArg(v_depth_4147_, v_keys_4148_, v_vals_4149_, v_i_4151_, v_entries_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_4154_, lean_object* v_depth_4155_, lean_object* v_keys_4156_, lean_object* v_vals_4157_, lean_object* v_heq_4158_, lean_object* v_i_4159_, lean_object* v_entries_4160_){
_start:
{
size_t v_depth_boxed_4161_; lean_object* v_res_4162_; 
v_depth_boxed_4161_ = lean_unbox_usize(v_depth_4155_);
lean_dec(v_depth_4155_);
v_res_4162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__4(v_00_u03b2_4154_, v_depth_boxed_4161_, v_keys_4156_, v_vals_4157_, v_heq_4158_, v_i_4159_, v_entries_4160_);
lean_dec_ref(v_vals_4157_);
lean_dec_ref(v_keys_4156_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___redArg(v___y_4168_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17___boxed(lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12_spec__17(v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(lean_object* v_00_u03b1_4179_, lean_object* v_x_4180_, lean_object* v_mkInfoTree_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___redArg(v_x_4180_, v_mkInfoTree_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4190_, lean_object* v_x_4191_, lean_object* v_mkInfoTree_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Term_withMacroExpansion___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__7_spec__9_spec__12(v_00_u03b1_4190_, v_x_4191_, v_mkInfoTree_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(lean_object* v_00_u03b2_4201_, lean_object* v_m_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___redArg(v_m_4202_, v_a_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18___boxed(lean_object* v_00_u03b2_4205_, lean_object* v_m_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18(v_00_u03b2_4205_, v_m_4206_, v_a_4207_);
lean_dec(v_a_4207_);
lean_dec_ref(v_m_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13(lean_object* v_00_u03b2_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_, lean_object* v_x_4212_, lean_object* v_x_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__0_spec__0_spec__3_spec__13___redArg(v_x_4210_, v_x_4211_, v_x_4212_, v_x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(lean_object* v_00_u03b2_4215_, lean_object* v_x_4216_, lean_object* v_x_4217_){
_start:
{
uint8_t v___x_4218_; 
v___x_4218_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___redArg(v_x_4216_, v_x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20___boxed(lean_object* v_00_u03b2_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_){
_start:
{
uint8_t v_res_4222_; lean_object* v_r_4223_; 
v_res_4222_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20(v_00_u03b2_4219_, v_x_4220_, v_x_4221_);
lean_dec_ref(v_x_4221_);
lean_dec_ref(v_x_4220_);
v_r_4223_ = lean_box(v_res_4222_);
return v_r_4223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(lean_object* v_00_u03b2_4224_, lean_object* v_a_4225_, lean_object* v_x_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___redArg(v_a_4225_, v_x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23___boxed(lean_object* v_00_u03b2_4228_, lean_object* v_a_4229_, lean_object* v_x_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__18_spec__23(v_00_u03b2_4228_, v_a_4229_, v_x_4230_);
lean_dec(v_x_4230_);
lean_dec(v_a_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(lean_object* v_00_u03b2_4232_, lean_object* v_x_4233_, size_t v_x_4234_, lean_object* v_x_4235_){
_start:
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___redArg(v_x_4233_, v_x_4234_, v_x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23___boxed(lean_object* v_00_u03b2_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_, lean_object* v_x_4240_){
_start:
{
size_t v_x_92417__boxed_4241_; uint8_t v_res_4242_; lean_object* v_r_4243_; 
v_x_92417__boxed_4241_ = lean_unbox_usize(v_x_4239_);
lean_dec(v_x_4239_);
v_res_4242_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23(v_00_u03b2_4237_, v_x_4238_, v_x_92417__boxed_4241_, v_x_4240_);
lean_dec_ref(v_x_4240_);
lean_dec_ref(v_x_4238_);
v_r_4243_ = lean_box(v_res_4242_);
return v_r_4243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(lean_object* v_00_u03b2_4244_, lean_object* v_keys_4245_, lean_object* v_vals_4246_, lean_object* v_heq_4247_, lean_object* v_i_4248_, lean_object* v_k_4249_){
_start:
{
uint8_t v___x_4250_; 
v___x_4250_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___redArg(v_keys_4245_, v_i_4248_, v_k_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26___boxed(lean_object* v_00_u03b2_4251_, lean_object* v_keys_4252_, lean_object* v_vals_4253_, lean_object* v_heq_4254_, lean_object* v_i_4255_, lean_object* v_k_4256_){
_start:
{
uint8_t v_res_4257_; lean_object* v_r_4258_; 
v_res_4257_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_elabDoLetOrReassign_spec__8_spec__12_spec__16_spec__20_spec__23_spec__26(v_00_u03b2_4251_, v_keys_4252_, v_vals_4253_, v_heq_4254_, v_i_4255_, v_k_4256_);
lean_dec_ref(v_k_4256_);
lean_dec_ref(v_vals_4253_);
lean_dec_ref(v_keys_4252_);
v_r_4258_ = lean_box(v_res_4257_);
return v_r_4258_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1(void){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__0));
v___x_4261_ = l_Lean_stringToMessageData(v___x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(lean_object* v_letConfigStx_4262_, lean_object* v_mutTk_x3f_4263_, lean_object* v_initConfig_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
if (lean_obj_tag(v_mutTk_x3f_4263_) == 0)
{
lean_object* v___x_4273_; 
v___x_4273_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4262_, v_initConfig_4264_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
return v___x_4273_;
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = l_Lean_Syntax_getArg(v_letConfigStx_4262_, v___x_4274_);
v___x_4276_ = l_Lean_Syntax_getArgs(v___x_4275_);
lean_dec(v___x_4275_);
v___x_4277_ = lean_array_get_size(v___x_4276_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = lean_nat_dec_eq(v___x_4277_, v___x_4274_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_initConfig_4264_);
v___x_4279_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___closed__1);
v___x_4280_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v_letConfigStx_4262_, v___x_4279_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
lean_dec(v_letConfigStx_4262_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
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
else
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_Elab_Term_mkLetConfig(v_letConfigStx_4262_, v_initConfig_4264_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
return v___x_4289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut___boxed(lean_object* v_letConfigStx_4290_, lean_object* v_mutTk_x3f_4291_, lean_object* v_initConfig_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_letConfigStx_4290_, v_mutTk_x3f_4291_, v_initConfig_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_mutTk_x3f_4291_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet(lean_object* v_stx_4317_, lean_object* v_dec_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
lean_inc(v_stx_4317_);
v___x_4328_ = l_Lean_Syntax_isOfKind(v_stx_4317_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
lean_dec_ref(v_dec_4318_);
lean_dec(v_stx_4317_);
v___x_4329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4329_;
}
else
{
lean_object* v___x_4330_; lean_object* v_tk_4331_; lean_object* v_mutTk_x3f_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___x_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4330_ = lean_unsigned_to_nat(0u);
v_tk_4331_ = l_Lean_Syntax_getArg(v_stx_4317_, v___x_4330_);
v___x_4365_ = lean_unsigned_to_nat(1u);
v___x_4366_ = l_Lean_Syntax_getArg(v_stx_4317_, v___x_4365_);
v___x_4367_ = l_Lean_Syntax_isNone(v___x_4366_);
if (v___x_4367_ == 0)
{
uint8_t v___x_4368_; 
lean_inc(v___x_4366_);
v___x_4368_ = l_Lean_Syntax_matchesNull(v___x_4366_, v___x_4365_);
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; 
lean_dec(v___x_4366_);
lean_dec(v_tk_4331_);
lean_dec_ref(v_dec_4318_);
lean_dec(v_stx_4317_);
v___x_4369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4369_;
}
else
{
lean_object* v_mutTk_x3f_4370_; lean_object* v___x_4371_; 
v_mutTk_x3f_4370_ = l_Lean_Syntax_getArg(v___x_4366_, v___x_4330_);
lean_dec(v___x_4366_);
v___x_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4371_, 0, v_mutTk_x3f_4370_);
v_mutTk_x3f_4333_ = v___x_4371_;
v___y_4334_ = v_a_4319_;
v___y_4335_ = v_a_4320_;
v___y_4336_ = v_a_4321_;
v___y_4337_ = v_a_4322_;
v___y_4338_ = v_a_4323_;
v___y_4339_ = v_a_4324_;
v___y_4340_ = v_a_4325_;
goto v___jp_4332_;
}
}
else
{
lean_object* v___x_4372_; 
lean_dec(v___x_4366_);
v___x_4372_ = lean_box(0);
v_mutTk_x3f_4333_ = v___x_4372_;
v___y_4334_ = v_a_4319_;
v___y_4335_ = v_a_4320_;
v___y_4336_ = v_a_4321_;
v___y_4337_ = v_a_4322_;
v___y_4338_ = v_a_4323_;
v___y_4339_ = v_a_4324_;
v___y_4340_ = v_a_4325_;
goto v___jp_4332_;
}
v___jp_4332_:
{
lean_object* v___x_4341_; lean_object* v_config_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4341_ = lean_unsigned_to_nat(2u);
v_config_4342_ = l_Lean_Syntax_getArg(v_stx_4317_, v___x_4341_);
v___x_4343_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_config_4342_);
v___x_4344_ = l_Lean_Syntax_isOfKind(v_config_4342_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_object* v___x_4345_; 
lean_dec(v_config_4342_);
lean_dec(v_mutTk_x3f_4333_);
lean_dec(v_tk_4331_);
lean_dec_ref(v_dec_4318_);
lean_dec(v_stx_4317_);
v___x_4345_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4345_;
}
else
{
lean_object* v___x_4346_; lean_object* v_decl_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4346_ = lean_unsigned_to_nat(3u);
v_decl_4347_ = l_Lean_Syntax_getArg(v_stx_4317_, v___x_4346_);
lean_dec(v_stx_4317_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4347_);
v___x_4349_ = l_Lean_Syntax_isOfKind(v_decl_4347_, v___x_4348_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_dec(v_decl_4347_);
lean_dec(v_config_4342_);
lean_dec(v_mutTk_x3f_4333_);
lean_dec(v_tk_4331_);
lean_dec_ref(v_dec_4318_);
v___x_4350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4350_;
}
else
{
uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4351_ = 0;
v___x_4352_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_4353_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_config_4342_, v_mutTk_x3f_4333_, v___x_4352_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4355_, 0, v_mutTk_x3f_4333_);
lean_ctor_set_uint8(v___x_4355_, sizeof(void*)*1, v___x_4351_);
v___x_4356_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4354_, v___x_4355_, v_decl_4347_, v_tk_4331_, v_dec_4318_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
return v___x_4356_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_decl_4347_);
lean_dec(v_mutTk_x3f_4333_);
lean_dec(v_tk_4331_);
lean_dec_ref(v_dec_4318_);
v_a_4357_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4353_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4353_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLet___boxed(lean_object* v_stx_4373_, lean_object* v_dec_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Elab_Do_elabDoLet(v_stx_4373_, v_dec_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec_ref(v_a_4375_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1(){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4391_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4392_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_4393_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___closed__1));
v___x_4394_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLet___boxed), 10, 0);
v___x_4395_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4391_, v___x_4392_, v___x_4393_, v___x_4394_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1___boxed(lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLet___regBuiltin_Lean_Elab_Do_elabDoLet__1();
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased(lean_object* v_stx_4412_, lean_object* v_dec_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4422_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
lean_inc(v_stx_4412_);
v___x_4423_ = l_Lean_Syntax_isOfKind(v_stx_4412_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; 
lean_dec_ref(v_dec_4413_);
lean_dec(v_stx_4412_);
v___x_4424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4424_;
}
else
{
lean_object* v___x_4425_; lean_object* v_tk_4426_; uint8_t v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v_t_x3f_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___x_4487_; lean_object* v_mutTk_x3f_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v___x_4425_ = lean_unsigned_to_nat(0u);
v_tk_4426_ = l_Lean_Syntax_getArg(v_stx_4412_, v___x_4425_);
v___x_4487_ = lean_unsigned_to_nat(1u);
v___x_4524_ = l_Lean_Syntax_getArg(v_stx_4412_, v___x_4487_);
v___x_4525_ = l_Lean_Syntax_isNone(v___x_4524_);
if (v___x_4525_ == 0)
{
uint8_t v___x_4526_; 
lean_inc(v___x_4524_);
v___x_4526_ = l_Lean_Syntax_matchesNull(v___x_4524_, v___x_4487_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_dec(v___x_4524_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
lean_dec(v_stx_4412_);
v___x_4527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4527_;
}
else
{
lean_object* v_mutTk_x3f_4528_; lean_object* v___x_4529_; 
v_mutTk_x3f_4528_ = l_Lean_Syntax_getArg(v___x_4524_, v___x_4425_);
lean_dec(v___x_4524_);
v___x_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4529_, 0, v_mutTk_x3f_4528_);
v_mutTk_x3f_4489_ = v___x_4529_;
v___y_4490_ = v_a_4414_;
v___y_4491_ = v_a_4415_;
v___y_4492_ = v_a_4416_;
v___y_4493_ = v_a_4417_;
v___y_4494_ = v_a_4418_;
v___y_4495_ = v_a_4419_;
v___y_4496_ = v_a_4420_;
goto v___jp_4488_;
}
}
else
{
lean_object* v___x_4530_; 
lean_dec(v___x_4524_);
v___x_4530_ = lean_box(0);
v_mutTk_x3f_4489_ = v___x_4530_;
v___y_4490_ = v_a_4414_;
v___y_4491_ = v_a_4415_;
v___y_4492_ = v_a_4416_;
v___y_4493_ = v_a_4417_;
v___y_4494_ = v_a_4418_;
v___y_4495_ = v_a_4419_;
v___y_4496_ = v_a_4420_;
goto v___jp_4488_;
}
v___jp_4427_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_inc_ref(v___y_4441_);
v___x_4446_ = l_Array_append___redArg(v___y_4441_, v___y_4445_);
lean_dec_ref(v___y_4445_);
lean_inc(v___y_4432_);
lean_inc_n(v___y_4443_, 3);
v___x_4447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4447_, 0, v___y_4443_);
lean_ctor_set(v___x_4447_, 1, v___y_4432_);
lean_ctor_set(v___x_4447_, 2, v___x_4446_);
v___x_4448_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___y_4443_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
lean_inc(v___y_4429_);
v___x_4450_ = l_Lean_Syntax_node5(v___y_4443_, v___y_4429_, v___y_4430_, v___y_4436_, v___x_4447_, v___x_4449_, v___y_4435_);
lean_inc(v___y_4440_);
v___x_4451_ = l_Lean_Syntax_node1(v___y_4443_, v___y_4440_, v___x_4450_);
v___x_4452_ = lean_box(0);
v___x_4453_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*1, v___y_4428_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*1 + 1, v___y_4428_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*1 + 2, v___y_4428_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*1 + 3, v___y_4428_);
lean_ctor_set_uint8(v___x_4453_, sizeof(void*)*1 + 4, v___y_4428_);
v___x_4454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4454_, 0, v___y_4433_);
lean_ctor_set_uint8(v___x_4454_, sizeof(void*)*1, v___x_4423_);
v___x_4455_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_4453_, v___x_4454_, v___x_4451_, v_tk_4426_, v_dec_4413_, v___y_4439_, v___y_4437_, v___y_4431_, v___y_4438_, v___y_4442_, v___y_4434_, v___y_4444_);
return v___x_4455_;
}
v___jp_4456_:
{
lean_object* v_ref_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; uint8_t v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_ref_4469_ = lean_ctor_get(v___y_4467_, 2);
v___x_4470_ = lean_unsigned_to_nat(4u);
v___x_4471_ = l_Lean_Syntax_getArg(v___y_4459_, v___x_4470_);
lean_dec(v___y_4459_);
v___x_4472_ = 0;
v___x_4473_ = l_Lean_SourceInfo_fromRef(v_ref_4469_, v___x_4472_);
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc(v___y_4458_);
lean_inc_n(v___x_4473_, 2);
v___x_4476_ = l_Lean_Syntax_node1(v___x_4473_, v___y_4458_, v___y_4457_);
v___x_4477_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4478_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_4479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4473_);
lean_ctor_set(v___x_4479_, 1, v___x_4477_);
lean_ctor_set(v___x_4479_, 2, v___x_4478_);
if (lean_obj_tag(v_t_x3f_4461_) == 1)
{
lean_object* v_val_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_val_4480_ = lean_ctor_get(v_t_x3f_4461_, 0);
lean_inc(v_val_4480_);
lean_dec_ref_known(v_t_x3f_4461_, 1);
v___x_4481_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_4473_, 2);
v___x_4483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4473_);
lean_ctor_set(v___x_4483_, 1, v___x_4482_);
v___x_4484_ = l_Lean_Syntax_node2(v___x_4473_, v___x_4481_, v___x_4483_, v_val_4480_);
v___x_4485_ = l_Array_mkArray1___redArg(v___x_4484_);
v___y_4428_ = v___x_4472_;
v___y_4429_ = v___x_4475_;
v___y_4430_ = v___x_4476_;
v___y_4431_ = v___y_4464_;
v___y_4432_ = v___x_4477_;
v___y_4433_ = v___y_4460_;
v___y_4434_ = v___y_4467_;
v___y_4435_ = v___x_4471_;
v___y_4436_ = v___x_4479_;
v___y_4437_ = v___y_4463_;
v___y_4438_ = v___y_4465_;
v___y_4439_ = v___y_4462_;
v___y_4440_ = v___x_4474_;
v___y_4441_ = v___x_4478_;
v___y_4442_ = v___y_4466_;
v___y_4443_ = v___x_4473_;
v___y_4444_ = v___y_4468_;
v___y_4445_ = v___x_4485_;
goto v___jp_4427_;
}
else
{
lean_object* v___x_4486_; 
lean_dec(v_t_x3f_4461_);
v___x_4486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4428_ = v___x_4472_;
v___y_4429_ = v___x_4475_;
v___y_4430_ = v___x_4476_;
v___y_4431_ = v___y_4464_;
v___y_4432_ = v___x_4477_;
v___y_4433_ = v___y_4460_;
v___y_4434_ = v___y_4467_;
v___y_4435_ = v___x_4471_;
v___y_4436_ = v___x_4479_;
v___y_4437_ = v___y_4463_;
v___y_4438_ = v___y_4465_;
v___y_4439_ = v___y_4462_;
v___y_4440_ = v___x_4474_;
v___y_4441_ = v___x_4478_;
v___y_4442_ = v___y_4466_;
v___y_4443_ = v___x_4473_;
v___y_4444_ = v___y_4468_;
v___y_4445_ = v___x_4486_;
goto v___jp_4427_;
}
}
v___jp_4488_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4497_ = lean_unsigned_to_nat(2u);
v___x_4498_ = l_Lean_Syntax_getArg(v_stx_4412_, v___x_4497_);
lean_dec(v_stx_4412_);
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_4498_);
v___x_4500_ = l_Lean_Syntax_isOfKind(v___x_4498_, v___x_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; 
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4501_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4502_ = l_Lean_Syntax_getArg(v___x_4498_, v___x_4425_);
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_4502_);
v___x_4504_ = l_Lean_Syntax_isOfKind(v___x_4502_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
lean_dec(v___x_4502_);
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4505_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4506_ = l_Lean_Syntax_getArg(v___x_4502_, v___x_4425_);
lean_dec(v___x_4502_);
v___x_4507_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4506_);
v___x_4508_ = l_Lean_Syntax_isOfKind(v___x_4506_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
lean_dec(v___x_4506_);
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = l_Lean_Syntax_getArg(v___x_4498_, v___x_4487_);
v___x_4511_ = l_Lean_Syntax_matchesNull(v___x_4510_, v___x_4425_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
lean_dec(v___x_4506_);
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4513_ = l_Lean_Syntax_getArg(v___x_4498_, v___x_4497_);
v___x_4514_ = l_Lean_Syntax_isNone(v___x_4513_);
if (v___x_4514_ == 0)
{
uint8_t v___x_4515_; 
lean_inc(v___x_4513_);
v___x_4515_ = l_Lean_Syntax_matchesNull(v___x_4513_, v___x_4487_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
lean_dec(v___x_4513_);
lean_dec(v___x_4506_);
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4516_;
}
else
{
lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4517_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4425_);
lean_dec(v___x_4513_);
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4517_);
v___x_4519_ = l_Lean_Syntax_isOfKind(v___x_4517_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; 
lean_dec(v___x_4517_);
lean_dec(v___x_4506_);
lean_dec(v___x_4498_);
lean_dec(v_mutTk_x3f_4489_);
lean_dec(v_tk_4426_);
lean_dec_ref(v_dec_4413_);
v___x_4520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4520_;
}
else
{
lean_object* v_t_x3f_4521_; lean_object* v___x_4522_; 
v_t_x3f_4521_ = l_Lean_Syntax_getArg(v___x_4517_, v___x_4487_);
lean_dec(v___x_4517_);
v___x_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4522_, 0, v_t_x3f_4521_);
v___y_4457_ = v___x_4506_;
v___y_4458_ = v___x_4503_;
v___y_4459_ = v___x_4498_;
v___y_4460_ = v_mutTk_x3f_4489_;
v_t_x3f_4461_ = v___x_4522_;
v___y_4462_ = v___y_4490_;
v___y_4463_ = v___y_4491_;
v___y_4464_ = v___y_4492_;
v___y_4465_ = v___y_4493_;
v___y_4466_ = v___y_4494_;
v___y_4467_ = v___y_4495_;
v___y_4468_ = v___y_4496_;
goto v___jp_4456_;
}
}
}
else
{
lean_object* v___x_4523_; 
lean_dec(v___x_4513_);
v___x_4523_ = lean_box(0);
v___y_4457_ = v___x_4506_;
v___y_4458_ = v___x_4503_;
v___y_4459_ = v___x_4498_;
v___y_4460_ = v_mutTk_x3f_4489_;
v_t_x3f_4461_ = v___x_4523_;
v___y_4462_ = v___y_4490_;
v___y_4463_ = v___y_4491_;
v___y_4464_ = v___y_4492_;
v___y_4465_ = v___y_4493_;
v___y_4466_ = v___y_4494_;
v___y_4467_ = v___y_4495_;
v___y_4468_ = v___y_4496_;
goto v___jp_4456_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoErased___boxed(lean_object* v_stx_4531_, lean_object* v_dec_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Elab_Do_elabDoErased(v_stx_4531_, v_dec_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1(){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4549_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4550_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___closed__1));
v___x_4552_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoErased___boxed), 10, 0);
v___x_4553_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4549_, v___x_4550_, v___x_4551_, v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1___boxed(lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0(lean_object* v_____do__lift_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = 0;
v___x_4560_ = l_Lean_SourceInfo_fromRef(v_____do__lift_4556_, v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v___y_4558_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___lam__0___boxed(lean_object* v_____do__lift_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_____do__lift_4562_, v___y_4563_, v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v_____do__lift_4562_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow(lean_object* v_stx_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; uint8_t v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___x_4651_; uint8_t v___x_4652_; 
v___x_4651_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
lean_inc(v_stx_4609_);
v___x_4652_ = l_Lean_Syntax_isOfKind(v_stx_4609_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
lean_dec(v_stx_4609_);
v___x_4653_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4611_);
return v___x_4653_;
}
else
{
lean_object* v___x_4654_; lean_object* v_tk_4655_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v_t_x3f_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; lean_object* v___x_4740_; lean_object* v_mutTk_x3f_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4654_ = lean_unsigned_to_nat(0u);
v_tk_4655_ = l_Lean_Syntax_getArg(v_stx_4609_, v___x_4654_);
v___x_4740_ = lean_unsigned_to_nat(1u);
v___x_4765_ = l_Lean_Syntax_getArg(v_stx_4609_, v___x_4740_);
v___x_4766_ = l_Lean_Syntax_isNone(v___x_4765_);
if (v___x_4766_ == 0)
{
uint8_t v___x_4767_; 
lean_inc(v___x_4765_);
v___x_4767_ = l_Lean_Syntax_matchesNull(v___x_4765_, v___x_4740_);
if (v___x_4767_ == 0)
{
lean_object* v___x_4768_; 
lean_dec(v___x_4765_);
lean_dec(v_tk_4655_);
lean_dec(v_stx_4609_);
v___x_4768_ = l_Lean_Macro_throwUnsupported___redArg(v_a_4611_);
return v___x_4768_;
}
else
{
lean_object* v_mutTk_x3f_4769_; lean_object* v___x_4770_; 
v_mutTk_x3f_4769_ = l_Lean_Syntax_getArg(v___x_4765_, v___x_4654_);
lean_dec(v___x_4765_);
v___x_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_mutTk_x3f_4769_);
v_mutTk_x3f_4742_ = v___x_4770_;
v___y_4743_ = v_a_4610_;
v___y_4744_ = v_a_4611_;
goto v___jp_4741_;
}
}
else
{
lean_object* v___x_4771_; 
lean_dec(v___x_4765_);
v___x_4771_ = lean_box(0);
v_mutTk_x3f_4742_ = v___x_4771_;
v___y_4743_ = v_a_4610_;
v___y_4744_ = v_a_4611_;
goto v___jp_4741_;
}
v___jp_4656_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v_a_4677_; lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4698_; 
lean_inc_ref(v___y_4662_);
v___x_4674_ = l_Array_append___redArg(v___y_4662_, v___y_4673_);
lean_dec_ref(v___y_4673_);
lean_inc(v___y_4657_);
lean_inc(v___y_4672_);
v___x_4675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4675_, 0, v___y_4672_);
lean_ctor_set(v___x_4675_, 1, v___y_4657_);
lean_ctor_set(v___x_4675_, 2, v___x_4674_);
v___x_4676_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v___y_4660_, v___y_4658_, v___y_4665_);
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_a_4678_ = lean_ctor_get(v___x_4676_, 1);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4680_ = v___x_4676_;
v_isShared_4681_ = v_isSharedCheck_4698_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4698_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4682_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__9));
lean_inc(v___y_4672_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 2);
lean_ctor_set(v___x_4680_, 1, v___x_4682_);
lean_ctor_set(v___x_4680_, 0, v___y_4672_);
v___x_4684_ = v___x_4680_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___y_4672_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_inc(v___y_4670_);
lean_inc(v___y_4663_);
lean_inc(v___y_4672_);
v___x_4685_ = l_Lean_Syntax_node4(v___y_4672_, v___y_4663_, v___y_4670_, v___x_4675_, v___x_4684_, v___y_4666_);
lean_inc(v___y_4667_);
v___x_4686_ = l_Lean_Syntax_node4(v___y_4672_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4664_, v___x_4685_);
v___x_4687_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__1));
v___x_4688_ = l_Lean_SourceInfo_fromRef(v_tk_4655_, v___x_4652_);
lean_dec(v_tk_4655_);
v___x_4689_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__10));
v___x_4690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4688_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
if (lean_obj_tag(v___y_4659_) == 1)
{
lean_object* v_val_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_val_4691_ = lean_ctor_get(v___y_4659_, 0);
lean_inc(v_val_4691_);
lean_dec_ref_known(v___y_4659_, 1);
v___x_4692_ = l_Lean_SourceInfo_fromRef(v_val_4691_, v___x_4652_);
lean_dec(v_val_4691_);
v___x_4693_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_4694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4692_);
lean_ctor_set(v___x_4694_, 1, v___x_4693_);
v___x_4695_ = l_Array_mkArray1___redArg(v___x_4694_);
v___y_4613_ = v___y_4657_;
v___y_4614_ = v_a_4678_;
v___y_4615_ = v___x_4686_;
v___y_4616_ = v___y_4660_;
v___y_4617_ = v___y_4661_;
v___y_4618_ = v___y_4662_;
v___y_4619_ = v___x_4690_;
v___y_4620_ = v___x_4687_;
v___y_4621_ = v___y_4670_;
v___y_4622_ = v___y_4671_;
v___y_4623_ = v_a_4677_;
v___y_4624_ = v___x_4695_;
goto v___jp_4612_;
}
else
{
lean_object* v___x_4696_; 
lean_dec(v___y_4659_);
v___x_4696_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4613_ = v___y_4657_;
v___y_4614_ = v_a_4678_;
v___y_4615_ = v___x_4686_;
v___y_4616_ = v___y_4660_;
v___y_4617_ = v___y_4661_;
v___y_4618_ = v___y_4662_;
v___y_4619_ = v___x_4690_;
v___y_4620_ = v___x_4687_;
v___y_4621_ = v___y_4670_;
v___y_4622_ = v___y_4671_;
v___y_4623_ = v_a_4677_;
v___y_4624_ = v___x_4696_;
goto v___jp_4612_;
}
}
}
}
v___jp_4699_:
{
lean_object* v_quotContext_4707_; lean_object* v_currMacroScope_4708_; lean_object* v_ref_4709_; lean_object* v___x_4710_; lean_object* v_a_4711_; lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4739_; 
v_quotContext_4707_ = lean_ctor_get(v___y_4705_, 1);
v_currMacroScope_4708_ = lean_ctor_get(v___y_4705_, 2);
v_ref_4709_ = lean_ctor_get(v___y_4705_, 5);
v___x_4710_ = l_Lean_Elab_Do_expandDoErasedArrow___lam__0(v_ref_4709_, v___y_4705_, v___y_4706_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_a_4712_ = lean_ctor_get(v___x_4710_, 1);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4714_ = v___x_4710_;
v_isShared_4715_ = v_isSharedCheck_4739_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4739_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; uint8_t v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4716_ = lean_unsigned_to_nat(3u);
v___x_4717_ = l_Lean_Syntax_getArg(v___y_4703_, v___x_4716_);
lean_dec(v___y_4703_);
v___x_4718_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
lean_inc(v_currMacroScope_4708_);
lean_inc(v_quotContext_4707_);
v___x_4719_ = l_Lean_addMacroScope(v_quotContext_4707_, v___x_4718_, v_currMacroScope_4708_);
v___x_4720_ = 0;
v___x_4721_ = l_Lean_mkIdentFrom(v___y_4702_, v___x_4719_, v___x_4720_);
v___x_4722_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_4723_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v_a_4711_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 2);
lean_ctor_set(v___x_4714_, 1, v___x_4723_);
v___x_4725_ = v___x_4714_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4711_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4726_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_4727_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v_a_4711_, 2);
v___x_4728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4728_, 0, v_a_4711_);
lean_ctor_set(v___x_4728_, 1, v___x_4726_);
lean_ctor_set(v___x_4728_, 2, v___x_4727_);
v___x_4729_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc_ref(v___x_4728_);
v___x_4730_ = l_Lean_Syntax_node1(v_a_4711_, v___x_4729_, v___x_4728_);
if (lean_obj_tag(v_t_x3f_4704_) == 1)
{
lean_object* v_val_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v_val_4731_ = lean_ctor_get(v_t_x3f_4704_, 0);
lean_inc(v_val_4731_);
lean_dec_ref_known(v_t_x3f_4704_, 1);
v___x_4732_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v_a_4711_, 2);
v___x_4734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4734_, 0, v_a_4711_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l_Lean_Syntax_node2(v_a_4711_, v___x_4732_, v___x_4734_, v_val_4731_);
v___x_4736_ = l_Array_mkArray1___redArg(v___x_4735_);
v___y_4657_ = v___x_4726_;
v___y_4658_ = v___y_4705_;
v___y_4659_ = v___y_4700_;
v___y_4660_ = v_ref_4709_;
v___y_4661_ = v___y_4702_;
v___y_4662_ = v___x_4727_;
v___y_4663_ = v___y_4701_;
v___y_4664_ = v___x_4730_;
v___y_4665_ = v_a_4712_;
v___y_4666_ = v___x_4717_;
v___y_4667_ = v___x_4722_;
v___y_4668_ = v___x_4725_;
v___y_4669_ = v___x_4728_;
v___y_4670_ = v___x_4721_;
v___y_4671_ = v___x_4720_;
v___y_4672_ = v_a_4711_;
v___y_4673_ = v___x_4736_;
goto v___jp_4656_;
}
else
{
lean_object* v___x_4737_; 
lean_dec(v_t_x3f_4704_);
v___x_4737_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_4657_ = v___x_4726_;
v___y_4658_ = v___y_4705_;
v___y_4659_ = v___y_4700_;
v___y_4660_ = v_ref_4709_;
v___y_4661_ = v___y_4702_;
v___y_4662_ = v___x_4727_;
v___y_4663_ = v___y_4701_;
v___y_4664_ = v___x_4730_;
v___y_4665_ = v_a_4712_;
v___y_4666_ = v___x_4717_;
v___y_4667_ = v___x_4722_;
v___y_4668_ = v___x_4725_;
v___y_4669_ = v___x_4728_;
v___y_4670_ = v___x_4721_;
v___y_4671_ = v___x_4720_;
v___y_4672_ = v_a_4711_;
v___y_4673_ = v___x_4737_;
goto v___jp_4656_;
}
}
}
}
v___jp_4741_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4745_ = lean_unsigned_to_nat(2u);
v___x_4746_ = l_Lean_Syntax_getArg(v_stx_4609_, v___x_4745_);
lean_dec(v_stx_4609_);
v___x_4747_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_4746_);
v___x_4748_ = l_Lean_Syntax_isOfKind(v___x_4746_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; 
lean_dec(v___x_4746_);
lean_dec(v_mutTk_x3f_4742_);
lean_dec(v_tk_4655_);
v___x_4749_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4744_);
return v___x_4749_;
}
else
{
lean_object* v___x_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; 
v___x_4750_ = l_Lean_Syntax_getArg(v___x_4746_, v___x_4654_);
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_4750_);
v___x_4752_ = l_Lean_Syntax_isOfKind(v___x_4750_, v___x_4751_);
if (v___x_4752_ == 0)
{
lean_object* v___x_4753_; 
lean_dec(v___x_4750_);
lean_dec(v___x_4746_);
lean_dec(v_mutTk_x3f_4742_);
lean_dec(v_tk_4655_);
v___x_4753_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4744_);
return v___x_4753_;
}
else
{
lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = l_Lean_Syntax_getArg(v___x_4746_, v___x_4740_);
v___x_4755_ = l_Lean_Syntax_isNone(v___x_4754_);
if (v___x_4755_ == 0)
{
uint8_t v___x_4756_; 
lean_inc(v___x_4754_);
v___x_4756_ = l_Lean_Syntax_matchesNull(v___x_4754_, v___x_4740_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
lean_dec(v___x_4754_);
lean_dec(v___x_4750_);
lean_dec(v___x_4746_);
lean_dec(v_mutTk_x3f_4742_);
lean_dec(v_tk_4655_);
v___x_4757_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4744_);
return v___x_4757_;
}
else
{
lean_object* v___x_4758_; lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4758_ = l_Lean_Syntax_getArg(v___x_4754_, v___x_4654_);
lean_dec(v___x_4754_);
v___x_4759_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_4758_);
v___x_4760_ = l_Lean_Syntax_isOfKind(v___x_4758_, v___x_4759_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
lean_dec(v___x_4758_);
lean_dec(v___x_4750_);
lean_dec(v___x_4746_);
lean_dec(v_mutTk_x3f_4742_);
lean_dec(v_tk_4655_);
v___x_4761_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4744_);
return v___x_4761_;
}
else
{
lean_object* v_t_x3f_4762_; lean_object* v___x_4763_; 
v_t_x3f_4762_ = l_Lean_Syntax_getArg(v___x_4758_, v___x_4740_);
lean_dec(v___x_4758_);
v___x_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4763_, 0, v_t_x3f_4762_);
v___y_4700_ = v_mutTk_x3f_4742_;
v___y_4701_ = v___x_4747_;
v___y_4702_ = v___x_4750_;
v___y_4703_ = v___x_4746_;
v_t_x3f_4704_ = v___x_4763_;
v___y_4705_ = v___y_4743_;
v___y_4706_ = v___y_4744_;
goto v___jp_4699_;
}
}
}
else
{
lean_object* v___x_4764_; 
lean_dec(v___x_4754_);
v___x_4764_ = lean_box(0);
v___y_4700_ = v_mutTk_x3f_4742_;
v___y_4701_ = v___x_4747_;
v___y_4702_ = v___x_4750_;
v___y_4703_ = v___x_4746_;
v_t_x3f_4704_ = v___x_4764_;
v___y_4705_ = v___y_4743_;
v___y_4706_ = v___y_4744_;
goto v___jp_4699_;
}
}
}
}
}
v___jp_4612_:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_inc_ref_n(v___y_4618_, 3);
v___x_4625_ = l_Array_append___redArg(v___y_4618_, v___y_4624_);
lean_dec_ref(v___y_4624_);
lean_inc_n(v___y_4613_, 5);
lean_inc_n(v___y_4623_, 5);
v___x_4626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4626_, 0, v___y_4623_);
lean_ctor_set(v___x_4626_, 1, v___y_4613_);
lean_ctor_set(v___x_4626_, 2, v___x_4625_);
v___x_4627_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_4628_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
v___x_4629_ = l_Lean_Syntax_node1(v___y_4623_, v___x_4628_, v___y_4617_);
v___x_4630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___y_4623_);
lean_ctor_set(v___x_4630_, 1, v___y_4613_);
lean_ctor_set(v___x_4630_, 2, v___y_4618_);
v___x_4631_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_4632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___y_4623_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
lean_inc_ref(v___x_4630_);
v___x_4633_ = l_Lean_Syntax_node5(v___y_4623_, v___x_4627_, v___x_4629_, v___x_4630_, v___x_4630_, v___x_4632_, v___y_4621_);
lean_inc(v___y_4620_);
v___x_4634_ = l_Lean_Syntax_node3(v___y_4623_, v___y_4620_, v___y_4619_, v___x_4626_, v___x_4633_);
v___x_4635_ = l_Lean_SourceInfo_fromRef(v___y_4616_, v___y_4622_);
v___x_4636_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_4637_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
lean_inc_n(v___x_4635_, 8);
v___x_4638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4635_);
lean_ctor_set(v___x_4638_, 1, v___x_4637_);
v___x_4639_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_4640_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_4641_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4635_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = l_Lean_Syntax_node1(v___x_4635_, v___y_4613_, v___x_4642_);
v___x_4644_ = l_Lean_Syntax_node2(v___x_4635_, v___x_4640_, v___y_4615_, v___x_4643_);
v___x_4645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4635_);
lean_ctor_set(v___x_4645_, 1, v___y_4613_);
lean_ctor_set(v___x_4645_, 2, v___y_4618_);
v___x_4646_ = l_Lean_Syntax_node2(v___x_4635_, v___x_4640_, v___x_4634_, v___x_4645_);
v___x_4647_ = l_Lean_Syntax_node2(v___x_4635_, v___y_4613_, v___x_4644_, v___x_4646_);
v___x_4648_ = l_Lean_Syntax_node1(v___x_4635_, v___x_4639_, v___x_4647_);
v___x_4649_ = l_Lean_Syntax_node2(v___x_4635_, v___x_4636_, v___x_4638_, v___x_4648_);
v___x_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
lean_ctor_set(v___x_4650_, 1, v___y_4614_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoErasedArrow___boxed(lean_object* v_stx_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Elab_Do_expandDoErasedArrow(v_stx_4772_, v_a_4773_, v_a_4774_);
lean_dec_ref(v_a_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1(){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4783_ = l_Lean_Elab_macroAttribute;
v___x_4784_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__8));
v___x_4785_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___closed__1));
v___x_4786_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoErasedArrow___boxed), 3, 0);
v___x_4787_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4783_, v___x_4784_, v___x_4785_, v___x_4786_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1___boxed(lean_object* v_a_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave(lean_object* v_stx_4796_, lean_object* v_dec_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; uint8_t v___x_4807_; 
v___x_4806_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
lean_inc(v_stx_4796_);
v___x_4807_ = l_Lean_Syntax_isOfKind(v_stx_4796_, v___x_4806_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
lean_dec_ref(v_dec_4797_);
lean_dec(v_stx_4796_);
v___x_4808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4808_;
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = l_Lean_Syntax_getArg(v_stx_4796_, v___x_4809_);
v___x_4811_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v___x_4810_);
v___x_4812_ = l_Lean_Syntax_isOfKind(v___x_4810_, v___x_4811_);
if (v___x_4812_ == 0)
{
lean_object* v___x_4813_; 
lean_dec(v___x_4810_);
lean_dec_ref(v_dec_4797_);
lean_dec(v_stx_4796_);
v___x_4813_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4813_;
}
else
{
lean_object* v___x_4814_; lean_object* v_decl_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v___x_4814_ = lean_unsigned_to_nat(2u);
v_decl_4815_ = l_Lean_Syntax_getArg(v_stx_4796_, v___x_4814_);
v___x_4816_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
lean_inc(v_decl_4815_);
v___x_4817_ = l_Lean_Syntax_isOfKind(v_decl_4815_, v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; 
lean_dec(v_decl_4815_);
lean_dec(v___x_4810_);
lean_dec_ref(v_dec_4797_);
lean_dec(v_stx_4796_);
v___x_4818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4818_;
}
else
{
lean_object* v___x_4819_; lean_object* v_tk_4820_; uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4819_ = lean_unsigned_to_nat(0u);
v_tk_4820_ = l_Lean_Syntax_getArg(v_stx_4796_, v___x_4819_);
lean_dec(v_stx_4796_);
v___x_4821_ = 0;
v___x_4822_ = lean_box(0);
v___x_4823_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1, v___x_4817_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1 + 1, v___x_4821_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1 + 2, v___x_4821_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1 + 3, v___x_4821_);
lean_ctor_set_uint8(v___x_4823_, sizeof(void*)*1 + 4, v___x_4821_);
v___x_4824_ = l_Lean_Elab_Term_mkLetConfig(v___x_4810_, v___x_4823_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v___x_4826_ = lean_box(1);
v___x_4827_ = l_Lean_Elab_Do_elabDoLetOrReassign(v_a_4825_, v___x_4826_, v_decl_4815_, v_tk_4820_, v_dec_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
return v___x_4827_;
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec(v_tk_4820_);
lean_dec(v_decl_4815_);
lean_dec_ref(v_dec_4797_);
v_a_4828_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4824_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4824_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoHave___boxed(lean_object* v_stx_4836_, lean_object* v_dec_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_Elab_Do_elabDoHave(v_stx_4836_, v_dec_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec_ref(v_a_4838_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1(){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4854_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4855_ = ((lean_object*)(l_Lean_Elab_Do_elabDoHave___closed__1));
v___x_4856_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___closed__1));
v___x_4857_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoHave___boxed), 10, 0);
v___x_4858_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4854_, v___x_4855_, v___x_4856_, v___x_4857_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1___boxed(lean_object* v_a_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoHave___regBuiltin_Lean_Elab_Do_elabDoHave__1();
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0(lean_object* v___x_4863_, lean_object* v___x_4864_, lean_object* v___x_4865_, lean_object* v___x_4866_, lean_object* v_decls_4867_, lean_object* v_a_4868_, uint8_t v___x_4869_, lean_object* v_body_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_ref_4879_; uint8_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v_ref_4879_ = lean_ctor_get(v___y_4876_, 2);
v___x_4880_ = 0;
v___x_4881_ = l_Lean_SourceInfo_fromRef(v_ref_4879_, v___x_4880_);
v___x_4882_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__0));
v___x_4883_ = l_Lean_Name_mkStr4(v___x_4863_, v___x_4864_, v___x_4865_, v___x_4882_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_4881_, 4);
v___x_4885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4881_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___closed__1));
v___x_4887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4881_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = l_Lean_Syntax_node2(v___x_4881_, v___x_4866_, v___x_4885_, v___x_4887_);
v___x_4889_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_4890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4881_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v___x_4891_ = l_Lean_Syntax_node4(v___x_4881_, v___x_4883_, v___x_4888_, v_decls_4867_, v___x_4890_, v_body_4870_);
v___x_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_a_4868_);
v___x_4893_ = l_Lean_Elab_Term_elabTerm(v___x_4891_, v___x_4892_, v___x_4869_, v___x_4869_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed(lean_object* v___x_4894_, lean_object* v___x_4895_, lean_object* v___x_4896_, lean_object* v___x_4897_, lean_object* v_decls_4898_, lean_object* v_a_4899_, lean_object* v___x_4900_, lean_object* v_body_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v___x_4492__boxed_4910_; lean_object* v_res_4911_; 
v___x_4492__boxed_4910_ = lean_unbox(v___x_4900_);
v_res_4911_ = l_Lean_Elab_Do_elabDoLetRec___lam__0(v___x_4894_, v___x_4895_, v___x_4896_, v___x_4897_, v_decls_4898_, v_a_4899_, v___x_4492__boxed_4910_, v_body_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
lean_dec_ref(v___y_4902_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
if (lean_obj_tag(v_a_4912_) == 0)
{
lean_object* v___x_4914_; 
v___x_4914_ = l_List_reverse___redArg(v_a_4913_);
return v___x_4914_;
}
else
{
lean_object* v_head_4915_; lean_object* v_tail_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4925_; 
v_head_4915_ = lean_ctor_get(v_a_4912_, 0);
v_tail_4916_ = lean_ctor_get(v_a_4912_, 1);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_a_4912_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4918_ = v_a_4912_;
v_isShared_4919_ = v_isSharedCheck_4925_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_tail_4916_);
lean_inc(v_head_4915_);
lean_dec(v_a_4912_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4925_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4920_; lean_object* v___x_4922_; 
v___x_4920_ = l_Lean_MessageData_ofSyntax(v_head_4915_);
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v_a_4913_);
lean_ctor_set(v___x_4918_, 0, v___x_4920_);
v___x_4922_ = v___x_4918_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4920_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v_a_4913_);
v___x_4922_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
v_a_4912_ = v_tail_4916_;
v_a_4913_ = v___x_4922_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetRec___closed__7(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__6));
v___x_4943_ = l_Lean_stringToMessageData(v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec(lean_object* v_stx_4944_, lean_object* v_dec_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; uint8_t v___x_4958_; 
v___x_4954_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_4955_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_4956_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_4957_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
lean_inc(v_stx_4944_);
v___x_4958_ = l_Lean_Syntax_isOfKind(v_stx_4944_, v___x_4957_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4959_; 
lean_dec_ref(v_dec_4945_);
lean_dec(v_stx_4944_);
v___x_4959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4959_;
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; uint8_t v___x_4963_; 
v___x_4960_ = lean_unsigned_to_nat(0u);
v___x_4961_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_4960_);
v___x_4962_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__3));
lean_inc(v___x_4961_);
v___x_4963_ = l_Lean_Syntax_isOfKind(v___x_4961_, v___x_4962_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; 
lean_dec(v___x_4961_);
lean_dec_ref(v_dec_4945_);
lean_dec(v_stx_4944_);
v___x_4964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4964_;
}
else
{
lean_object* v___x_4965_; lean_object* v_decls_4966_; lean_object* v___x_4967_; uint8_t v___x_4968_; 
v___x_4965_ = lean_unsigned_to_nat(1u);
v_decls_4966_ = l_Lean_Syntax_getArg(v_stx_4944_, v___x_4965_);
lean_dec(v_stx_4944_);
v___x_4967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__5));
lean_inc(v_decls_4966_);
v___x_4968_ = l_Lean_Syntax_isOfKind(v_decls_4966_, v___x_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; 
lean_dec(v_decls_4966_);
lean_dec(v___x_4961_);
lean_dec_ref(v_dec_4945_);
v___x_4969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_4969_;
}
else
{
lean_object* v_tk_4970_; lean_object* v___x_4971_; 
v_tk_4970_ = l_Lean_Syntax_getArg(v___x_4961_, v___x_4960_);
lean_dec(v___x_4961_);
v___x_4971_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4945_, v_tk_4970_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
lean_dec(v_tk_4970_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4973_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref_known(v___x_4971_, 1);
lean_inc(v_decls_4966_);
v___x_4973_ = l_Lean_Elab_Do_getLetRecDeclsVars(v_decls_4966_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v_doBlockResultType_4975_; lean_object* v___x_4976_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
v_doBlockResultType_4975_ = lean_ctor_get(v_a_4946_, 3);
lean_inc_ref(v_doBlockResultType_4975_);
v___x_4976_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4975_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___x_4978_; lean_object* v___f_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
v___x_4978_ = lean_box(v___x_4968_);
v___f_4979_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___lam__0___boxed), 16, 7);
lean_closure_set(v___f_4979_, 0, v___x_4954_);
lean_closure_set(v___f_4979_, 1, v___x_4955_);
lean_closure_set(v___f_4979_, 2, v___x_4956_);
lean_closure_set(v___f_4979_, 3, v___x_4962_);
lean_closure_set(v___f_4979_, 4, v_decls_4966_);
lean_closure_set(v___f_4979_, 5, v_a_4977_);
lean_closure_set(v___f_4979_, 6, v___x_4978_);
v___x_4980_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetRec___closed__7, &l_Lean_Elab_Do_elabDoLetRec___closed__7_once, _init_l_Lean_Elab_Do_elabDoLetRec___closed__7);
v___x_4981_ = lean_array_to_list(v_a_4974_);
v___x_4982_ = lean_box(0);
v___x_4983_ = l_List_mapTR_loop___at___00Lean_Elab_Do_elabDoLetRec_spec__0(v___x_4981_, v___x_4982_);
v___x_4984_ = l_Lean_MessageData_ofList(v___x_4983_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4980_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
v___x_4986_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_4986_, 0, v_a_4972_);
v___x_4987_ = lean_box(0);
v___x_4988_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_4985_, v___x_4986_, v___f_4979_, v___x_4987_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_4988_;
}
else
{
lean_dec(v_a_4974_);
lean_dec(v_a_4972_);
lean_dec(v_decls_4966_);
return v___x_4976_;
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec(v_a_4972_);
lean_dec(v_decls_4966_);
v_a_4989_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4973_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4973_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec(v_decls_4966_);
v_a_4997_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4971_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4971_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetRec___boxed(lean_object* v_stx_5005_, lean_object* v_dec_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Lean_Elab_Do_elabDoLetRec(v_stx_5005_, v_dec_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec_ref(v_a_5007_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1(){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5023_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5024_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetRec___closed__1));
v___x_5025_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___closed__1));
v___x_5026_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetRec___boxed), 10, 0);
v___x_5027_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5023_, v___x_5024_, v___x_5025_, v___x_5026_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1___boxed(lean_object* v_a_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetRec___regBuiltin_Lean_Elab_Do_elabDoLetRec__1();
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign(lean_object* v_stx_5036_, lean_object* v_dec_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_){
_start:
{
lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___y_5055_; lean_object* v___y_5056_; uint8_t v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___x_5079_; uint8_t v___x_5080_; 
v___x_5079_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
lean_inc(v_stx_5036_);
v___x_5080_ = l_Lean_Syntax_isOfKind(v_stx_5036_, v___x_5079_);
if (v___x_5080_ == 0)
{
lean_object* v___x_5081_; 
lean_dec_ref(v_dec_5037_);
lean_dec(v_stx_5036_);
v___x_5081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5081_;
}
else
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; 
v___x_5082_ = lean_unsigned_to_nat(0u);
v___x_5083_ = l_Lean_Syntax_getArg(v_stx_5036_, v___x_5082_);
lean_dec(v_stx_5036_);
v___x_5084_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
lean_inc(v___x_5083_);
v___x_5085_ = l_Lean_Syntax_isOfKind(v___x_5083_, v___x_5084_);
if (v___x_5085_ == 0)
{
if (v___x_5085_ == 0)
{
lean_object* v___x_5097_; uint8_t v___x_5098_; 
v___x_5097_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
lean_inc(v___x_5083_);
v___x_5098_ = l_Lean_Syntax_isOfKind(v___x_5083_, v___x_5097_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; 
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5099_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5099_;
}
else
{
goto v___jp_5086_;
}
}
else
{
goto v___jp_5086_;
}
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5100_ = l_Lean_Syntax_getArg(v___x_5083_, v___x_5082_);
v___x_5101_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc(v___x_5100_);
v___x_5102_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; 
lean_dec(v___x_5100_);
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5103_;
}
else
{
lean_object* v___x_5104_; lean_object* v_xType_x3f_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___x_5133_; uint8_t v___x_5134_; 
v___x_5104_ = l_Lean_Syntax_getArg(v___x_5100_, v___x_5082_);
lean_dec(v___x_5100_);
v___x_5133_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_5104_);
v___x_5134_ = l_Lean_Syntax_isOfKind(v___x_5104_, v___x_5133_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; 
lean_dec(v___x_5104_);
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5135_;
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; uint8_t v___x_5138_; 
v___x_5136_ = lean_unsigned_to_nat(1u);
v___x_5137_ = l_Lean_Syntax_getArg(v___x_5083_, v___x_5136_);
v___x_5138_ = l_Lean_Syntax_matchesNull(v___x_5137_, v___x_5082_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; 
lean_dec(v___x_5104_);
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5139_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5139_;
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; 
v___x_5140_ = lean_unsigned_to_nat(2u);
v___x_5141_ = l_Lean_Syntax_getArg(v___x_5083_, v___x_5140_);
v___x_5142_ = l_Lean_Syntax_isNone(v___x_5141_);
if (v___x_5142_ == 0)
{
uint8_t v___x_5143_; 
lean_inc(v___x_5141_);
v___x_5143_ = l_Lean_Syntax_matchesNull(v___x_5141_, v___x_5136_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
lean_dec(v___x_5141_);
lean_dec(v___x_5104_);
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5144_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5144_;
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5146_; uint8_t v___x_5147_; 
v___x_5145_ = l_Lean_Syntax_getArg(v___x_5141_, v___x_5082_);
lean_dec(v___x_5141_);
v___x_5146_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_5145_);
v___x_5147_ = l_Lean_Syntax_isOfKind(v___x_5145_, v___x_5146_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; 
lean_dec(v___x_5145_);
lean_dec(v___x_5104_);
lean_dec(v___x_5083_);
lean_dec_ref(v_dec_5037_);
v___x_5148_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5148_;
}
else
{
lean_object* v_xType_x3f_5149_; lean_object* v___x_5150_; 
v_xType_x3f_5149_ = l_Lean_Syntax_getArg(v___x_5145_, v___x_5136_);
lean_dec(v___x_5145_);
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v_xType_x3f_5149_);
v_xType_x3f_5106_ = v___x_5150_;
v___y_5107_ = v_a_5038_;
v___y_5108_ = v_a_5039_;
v___y_5109_ = v_a_5040_;
v___y_5110_ = v_a_5041_;
v___y_5111_ = v_a_5042_;
v___y_5112_ = v_a_5043_;
v___y_5113_ = v_a_5044_;
goto v___jp_5105_;
}
}
}
else
{
lean_object* v___x_5151_; 
lean_dec(v___x_5141_);
v___x_5151_ = lean_box(0);
v_xType_x3f_5106_ = v___x_5151_;
v___y_5107_ = v_a_5038_;
v___y_5108_ = v_a_5039_;
v___y_5109_ = v_a_5040_;
v___y_5110_ = v_a_5041_;
v___y_5111_ = v_a_5042_;
v___y_5112_ = v_a_5043_;
v___y_5113_ = v_a_5044_;
goto v___jp_5105_;
}
}
}
v___jp_5105_:
{
lean_object* v_ref_5114_; lean_object* v___x_5115_; lean_object* v_tk_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v_ref_5114_ = lean_ctor_get(v___y_5112_, 2);
v___x_5115_ = lean_unsigned_to_nat(3u);
v_tk_5116_ = l_Lean_Syntax_getArg(v___x_5083_, v___x_5115_);
v___x_5117_ = lean_unsigned_to_nat(4u);
v___x_5118_ = l_Lean_Syntax_getArg(v___x_5083_, v___x_5117_);
lean_dec(v___x_5083_);
v___x_5119_ = 0;
v___x_5120_ = l_Lean_SourceInfo_fromRef(v_ref_5114_, v___x_5119_);
v___x_5121_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
lean_inc_n(v___x_5120_, 2);
v___x_5122_ = l_Lean_Syntax_node1(v___x_5120_, v___x_5101_, v___x_5104_);
v___x_5123_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5124_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5125_, 0, v___x_5120_);
lean_ctor_set(v___x_5125_, 1, v___x_5123_);
lean_ctor_set(v___x_5125_, 2, v___x_5124_);
if (lean_obj_tag(v_xType_x3f_5106_) == 1)
{
lean_object* v_val_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v_val_5126_ = lean_ctor_get(v_xType_x3f_5106_, 0);
lean_inc(v_val_5126_);
lean_dec_ref_known(v_xType_x3f_5106_, 1);
v___x_5127_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
v___x_5128_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
lean_inc_n(v___x_5120_, 2);
v___x_5129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5120_);
lean_ctor_set(v___x_5129_, 1, v___x_5128_);
v___x_5130_ = l_Lean_Syntax_node2(v___x_5120_, v___x_5127_, v___x_5129_, v_val_5126_);
v___x_5131_ = l_Array_mkArray1___redArg(v___x_5130_);
v___y_5047_ = v___x_5125_;
v___y_5048_ = v___x_5123_;
v___y_5049_ = v___y_5111_;
v___y_5050_ = v_tk_5116_;
v___y_5051_ = v___y_5108_;
v___y_5052_ = v___y_5110_;
v___y_5053_ = v___x_5120_;
v___y_5054_ = v___y_5112_;
v___y_5055_ = v___x_5122_;
v___y_5056_ = v___y_5107_;
v___y_5057_ = v___x_5119_;
v___y_5058_ = v___x_5124_;
v___y_5059_ = v___y_5109_;
v___y_5060_ = v___y_5113_;
v___y_5061_ = v___x_5121_;
v___y_5062_ = v___x_5118_;
v___y_5063_ = v___x_5131_;
goto v___jp_5046_;
}
else
{
lean_object* v___x_5132_; 
lean_dec(v_xType_x3f_5106_);
v___x_5132_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__2));
v___y_5047_ = v___x_5125_;
v___y_5048_ = v___x_5123_;
v___y_5049_ = v___y_5111_;
v___y_5050_ = v_tk_5116_;
v___y_5051_ = v___y_5108_;
v___y_5052_ = v___y_5110_;
v___y_5053_ = v___x_5120_;
v___y_5054_ = v___y_5112_;
v___y_5055_ = v___x_5122_;
v___y_5056_ = v___y_5107_;
v___y_5057_ = v___x_5119_;
v___y_5058_ = v___x_5124_;
v___y_5059_ = v___y_5109_;
v___y_5060_ = v___y_5113_;
v___y_5061_ = v___x_5121_;
v___y_5062_ = v___x_5118_;
v___y_5063_ = v___x_5132_;
goto v___jp_5046_;
}
}
}
}
v___jp_5086_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v_decl_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5087_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5088_ = lean_unsigned_to_nat(1u);
v___x_5089_ = lean_mk_empty_array_with_capacity(v___x_5088_);
v___x_5090_ = lean_array_push(v___x_5089_, v___x_5083_);
v___x_5091_ = lean_box(2);
v_decl_5092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_decl_5092_, 0, v___x_5091_);
lean_ctor_set(v_decl_5092_, 1, v___x_5087_);
lean_ctor_set(v_decl_5092_, 2, v___x_5090_);
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*1, v___x_5085_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*1 + 1, v___x_5085_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*1 + 2, v___x_5085_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*1 + 3, v___x_5085_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*1 + 4, v___x_5085_);
v___x_5095_ = lean_box(2);
lean_inc_ref(v_decl_5092_);
v___x_5096_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5094_, v___x_5095_, v_decl_5092_, v_decl_5092_, v_dec_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_);
return v___x_5096_;
}
}
v___jp_5046_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_inc_ref(v___y_5058_);
v___x_5064_ = l_Array_append___redArg(v___y_5058_, v___y_5063_);
lean_dec_ref(v___y_5063_);
lean_inc(v___y_5048_);
lean_inc_n(v___y_5053_, 2);
v___x_5065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5065_, 0, v___y_5053_);
lean_ctor_set(v___x_5065_, 1, v___y_5048_);
lean_ctor_set(v___x_5065_, 2, v___x_5064_);
v___x_5066_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___y_5053_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
lean_inc(v___y_5061_);
v___x_5068_ = l_Lean_Syntax_node5(v___y_5053_, v___y_5061_, v___y_5055_, v___y_5047_, v___x_5065_, v___x_5067_, v___y_5062_);
v___x_5069_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5070_ = lean_unsigned_to_nat(1u);
v___x_5071_ = lean_mk_empty_array_with_capacity(v___x_5070_);
v___x_5072_ = lean_array_push(v___x_5071_, v___x_5068_);
v___x_5073_ = lean_box(2);
v___x_5074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
lean_ctor_set(v___x_5074_, 1, v___x_5069_);
lean_ctor_set(v___x_5074_, 2, v___x_5072_);
v___x_5075_ = lean_box(0);
v___x_5076_ = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*1, v___y_5057_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*1 + 1, v___y_5057_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*1 + 2, v___y_5057_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*1 + 3, v___y_5057_);
lean_ctor_set_uint8(v___x_5076_, sizeof(void*)*1 + 4, v___y_5057_);
v___x_5077_ = lean_box(2);
v___x_5078_ = l_Lean_Elab_Do_elabDoLetOrReassign(v___x_5076_, v___x_5077_, v___x_5074_, v___y_5050_, v_dec_5037_, v___y_5056_, v___y_5051_, v___y_5059_, v___y_5052_, v___y_5049_, v___y_5054_, v___y_5060_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassign___boxed(lean_object* v_stx_5152_, lean_object* v_dec_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l_Lean_Elab_Do_elabDoReassign(v_stx_5152_, v_dec_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec_ref(v_a_5154_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1(){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5170_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5171_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_5172_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___closed__1));
v___x_5173_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassign___boxed), 10, 0);
v___x_5174_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5170_, v___x_5171_, v___x_5172_, v___x_5173_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1___boxed(lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassign___regBuiltin_Lean_Elab_Do_elabDoReassign__1();
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0(lean_object* v_____do__lift_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
uint8_t v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5186_ = 0;
v___x_5187_ = l_Lean_SourceInfo_fromRef(v_____do__lift_5177_, v___x_5186_);
v___x_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5187_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___lam__0___boxed(lean_object* v_____do__lift_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_____do__lift_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v_____do__lift_5189_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(lean_object* v_as_5199_, size_t v_sz_5200_, size_t v_i_5201_, lean_object* v_b_5202_, lean_object* v___y_5203_){
_start:
{
uint8_t v___x_5205_; 
v___x_5205_ = lean_usize_dec_lt(v_i_5201_, v_sz_5200_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5206_, 0, v_b_5202_);
return v___x_5206_;
}
else
{
lean_object* v_ref_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v_a_5210_; uint8_t v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; size_t v___x_5244_; size_t v___x_5245_; 
v_ref_5207_ = lean_ctor_get(v___y_5203_, 2);
v___x_5208_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5209_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5210_ = lean_array_uget_borrowed(v_as_5199_, v_i_5201_);
v___x_5211_ = 0;
v___x_5212_ = l_Lean_SourceInfo_fromRef(v_ref_5207_, v___x_5211_);
v___x_5213_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5214_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5215_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5216_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5212_, 17);
v___x_5217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5212_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5212_);
lean_ctor_set(v___x_5219_, 1, v___x_5218_);
v___x_5220_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5213_, v___x_5219_);
v___x_5221_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5212_);
lean_ctor_set(v___x_5222_, 1, v___x_5213_);
lean_ctor_set(v___x_5222_, 2, v___x_5221_);
lean_inc_ref_n(v___x_5222_, 3);
v___x_5223_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5208_, v___x_5222_);
v___x_5224_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5225_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5226_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5210_, 2);
v___x_5227_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5226_, v_a_5210_);
v___x_5228_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5212_);
lean_ctor_set(v___x_5229_, 1, v___x_5228_);
v___x_5230_ = l_Lean_Syntax_node5(v___x_5212_, v___x_5225_, v___x_5227_, v___x_5222_, v___x_5222_, v___x_5229_, v_a_5210_);
v___x_5231_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5224_, v___x_5230_);
v___x_5232_ = l_Lean_Syntax_node4(v___x_5212_, v___x_5215_, v___x_5217_, v___x_5220_, v___x_5223_, v___x_5231_);
v___x_5233_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5212_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
v___x_5235_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5213_, v___x_5234_);
v___x_5236_ = l_Lean_Syntax_node2(v___x_5212_, v___x_5214_, v___x_5232_, v___x_5235_);
v___x_5237_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5238_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5212_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = l_Lean_Syntax_node2(v___x_5212_, v___x_5237_, v___x_5239_, v_b_5202_);
v___x_5241_ = l_Lean_Syntax_node2(v___x_5212_, v___x_5214_, v___x_5240_, v___x_5222_);
v___x_5242_ = l_Lean_Syntax_node2(v___x_5212_, v___x_5213_, v___x_5236_, v___x_5241_);
v___x_5243_ = l_Lean_Syntax_node1(v___x_5212_, v___x_5209_, v___x_5242_);
v___x_5244_ = ((size_t)1ULL);
v___x_5245_ = lean_usize_add(v_i_5201_, v___x_5244_);
v_i_5201_ = v___x_5245_;
v_b_5202_ = v___x_5243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg___boxed(lean_object* v_as_5247_, lean_object* v_sz_5248_, lean_object* v_i_5249_, lean_object* v_b_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
size_t v_sz_boxed_5253_; size_t v_i_boxed_5254_; lean_object* v_res_5255_; 
v_sz_boxed_5253_ = lean_unbox_usize(v_sz_5248_);
lean_dec(v_sz_5248_);
v_i_boxed_5254_ = lean_unbox_usize(v_i_5249_);
lean_dec(v_i_5249_);
v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5247_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5250_, v___y_5251_);
lean_dec_ref(v___y_5251_);
lean_dec_ref(v_as_5247_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(lean_object* v_as_5256_, size_t v_sz_5257_, size_t v_i_5258_, lean_object* v_b_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
uint8_t v___x_5268_; 
v___x_5268_ = lean_usize_dec_lt(v_i_5258_, v_sz_5257_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v_b_5259_);
return v___x_5269_;
}
else
{
lean_object* v_ref_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v_a_5273_; uint8_t v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; size_t v___x_5307_; size_t v___x_5308_; lean_object* v___x_5309_; 
v_ref_5270_ = lean_ctor_get(v___y_5265_, 2);
v___x_5271_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
v___x_5272_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v_a_5273_ = lean_array_uget_borrowed(v_as_5256_, v_i_5258_);
v___x_5274_ = 0;
v___x_5275_ = l_Lean_SourceInfo_fromRef(v_ref_5270_, v___x_5274_);
v___x_5276_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5277_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5278_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__1));
v___x_5279_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc_n(v___x_5275_, 17);
v___x_5280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5275_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5275_);
lean_ctor_set(v___x_5282_, 1, v___x_5281_);
v___x_5283_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5276_, v___x_5282_);
v___x_5284_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5285_, 0, v___x_5275_);
lean_ctor_set(v___x_5285_, 1, v___x_5276_);
lean_ctor_set(v___x_5285_, 2, v___x_5284_);
lean_inc_ref_n(v___x_5285_, 3);
v___x_5286_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5271_, v___x_5285_);
v___x_5287_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__4));
v___x_5288_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__8));
v___x_5289_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v_a_5273_, 2);
v___x_5290_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5289_, v_a_5273_);
v___x_5291_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5275_);
lean_ctor_set(v___x_5292_, 1, v___x_5291_);
v___x_5293_ = l_Lean_Syntax_node5(v___x_5275_, v___x_5288_, v___x_5290_, v___x_5285_, v___x_5285_, v___x_5292_, v_a_5273_);
v___x_5294_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5287_, v___x_5293_);
v___x_5295_ = l_Lean_Syntax_node4(v___x_5275_, v___x_5278_, v___x_5280_, v___x_5283_, v___x_5286_, v___x_5294_);
v___x_5296_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__7));
v___x_5297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5275_);
lean_ctor_set(v___x_5297_, 1, v___x_5296_);
v___x_5298_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5276_, v___x_5297_);
v___x_5299_ = l_Lean_Syntax_node2(v___x_5275_, v___x_5277_, v___x_5295_, v___x_5298_);
v___x_5300_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__1));
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__2));
v___x_5302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5302_, 0, v___x_5275_);
lean_ctor_set(v___x_5302_, 1, v___x_5301_);
v___x_5303_ = l_Lean_Syntax_node2(v___x_5275_, v___x_5300_, v___x_5302_, v_b_5259_);
v___x_5304_ = l_Lean_Syntax_node2(v___x_5275_, v___x_5277_, v___x_5303_, v___x_5285_);
v___x_5305_ = l_Lean_Syntax_node2(v___x_5275_, v___x_5276_, v___x_5299_, v___x_5304_);
v___x_5306_ = l_Lean_Syntax_node1(v___x_5275_, v___x_5272_, v___x_5305_);
v___x_5307_ = ((size_t)1ULL);
v___x_5308_ = lean_usize_add(v_i_5258_, v___x_5307_);
v___x_5309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5256_, v_sz_5257_, v___x_5308_, v___x_5306_, v___y_5265_);
return v___x_5309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0___boxed(lean_object* v_as_5310_, lean_object* v_sz_5311_, lean_object* v_i_5312_, lean_object* v_b_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
size_t v_sz_boxed_5322_; size_t v_i_boxed_5323_; lean_object* v_res_5324_; 
v_sz_boxed_5322_ = lean_unbox_usize(v_sz_5311_);
lean_dec(v_sz_5311_);
v_i_boxed_5323_ = lean_unbox_usize(v_i_5312_);
lean_dec(v_i_5312_);
v_res_5324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v_as_5310_, v_sz_boxed_5322_, v_i_boxed_5323_, v_b_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec_ref(v_as_5310_);
return v_res_5324_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__11(void){
_start:
{
lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5364_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__10));
v___x_5365_ = l_String_toRawSubstring_x27(v___x_5364_);
return v___x_5365_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetElse___closed__18(void){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5379_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__17));
v___x_5380_ = l_String_toRawSubstring_x27(v___x_5379_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse(lean_object* v_stx_5397_, lean_object* v_dec_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v___x_5407_; uint8_t v___x_5408_; 
v___x_5407_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
lean_inc(v_stx_5397_);
v___x_5408_ = l_Lean_Syntax_isOfKind(v_stx_5397_, v___x_5407_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; 
lean_dec_ref(v_dec_5398_);
lean_dec(v_stx_5397_);
v___x_5409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5409_;
}
else
{
lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5413_; uint8_t v___y_5414_; lean_object* v___y_5415_; lean_object* v_body_5416_; lean_object* v___y_5417_; lean_object* v___y_5418_; lean_object* v___y_5419_; lean_object* v___y_5420_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v___y_5423_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; uint8_t v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5505_; lean_object* v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; lean_object* v_a_5511_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___y_5532_; lean_object* v___y_5533_; lean_object* v___y_5534_; lean_object* v___y_5535_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v_mutTk_x3f_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; lean_object* v___x_5641_; lean_object* v___x_5642_; uint8_t v___x_5643_; 
v___x_5641_ = lean_unsigned_to_nat(1u);
v___x_5642_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5641_);
v___x_5643_ = l_Lean_Syntax_isNone(v___x_5642_);
if (v___x_5643_ == 0)
{
uint8_t v___x_5644_; 
lean_inc(v___x_5642_);
v___x_5644_ = l_Lean_Syntax_matchesNull(v___x_5642_, v___x_5641_);
if (v___x_5644_ == 0)
{
lean_object* v___x_5645_; 
lean_dec(v___x_5642_);
lean_dec_ref(v_dec_5398_);
lean_dec(v_stx_5397_);
v___x_5645_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5645_;
}
else
{
lean_object* v___x_5646_; lean_object* v_mutTk_x3f_5647_; lean_object* v___x_5648_; 
v___x_5646_ = lean_unsigned_to_nat(0u);
v_mutTk_x3f_5647_ = l_Lean_Syntax_getArg(v___x_5642_, v___x_5646_);
lean_dec(v___x_5642_);
v___x_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5648_, 0, v_mutTk_x3f_5647_);
v_mutTk_x3f_5610_ = v___x_5648_;
v___y_5611_ = v_a_5399_;
v___y_5612_ = v_a_5400_;
v___y_5613_ = v_a_5401_;
v___y_5614_ = v_a_5402_;
v___y_5615_ = v_a_5403_;
v___y_5616_ = v_a_5404_;
v___y_5617_ = v_a_5405_;
goto v___jp_5609_;
}
}
else
{
lean_object* v___x_5649_; 
lean_dec(v___x_5642_);
v___x_5649_ = lean_box(0);
v_mutTk_x3f_5610_ = v___x_5649_;
v___y_5611_ = v_a_5399_;
v___y_5612_ = v_a_5400_;
v___y_5613_ = v_a_5401_;
v___y_5614_ = v_a_5402_;
v___y_5615_ = v_a_5403_;
v___y_5616_ = v_a_5404_;
v___y_5617_ = v_a_5405_;
goto v___jp_5609_;
}
v___jp_5410_:
{
lean_object* v_eq_x3f_5424_; 
v_eq_x3f_5424_ = lean_ctor_get(v___y_5411_, 0);
lean_inc(v_eq_x3f_5424_);
lean_dec_ref(v___y_5411_);
if (lean_obj_tag(v_eq_x3f_5424_) == 1)
{
lean_object* v_val_5425_; lean_object* v_ref_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v_val_5425_ = lean_ctor_get(v_eq_x3f_5424_, 0);
lean_inc(v_val_5425_);
lean_dec_ref_known(v_eq_x3f_5424_, 1);
v_ref_5426_ = lean_ctor_get(v___y_5422_, 2);
v___x_5427_ = l_Lean_SourceInfo_fromRef(v_ref_5426_, v___y_5414_);
v___x_5428_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5429_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
lean_inc_n(v___x_5427_, 19);
v___x_5430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5427_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5432_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5427_);
lean_ctor_set(v___x_5433_, 1, v___x_5431_);
lean_ctor_set(v___x_5433_, 2, v___x_5432_);
v___x_5434_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
v___x_5435_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__36));
v___x_5436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5427_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
v___x_5437_ = l_Lean_Syntax_node2(v___x_5427_, v___x_5431_, v_val_5425_, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_node2(v___x_5427_, v___x_5434_, v___x_5437_, v___y_5413_);
v___x_5439_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5431_, v___x_5438_);
v___x_5440_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5427_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5443_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5444_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5427_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5431_, v___y_5412_);
v___x_5447_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5431_, v___x_5446_);
v___x_5448_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5427_);
lean_ctor_set(v___x_5449_, 1, v___x_5448_);
lean_inc_ref(v___x_5449_);
lean_inc_ref(v___x_5445_);
v___x_5450_ = l_Lean_Syntax_node4(v___x_5427_, v___x_5443_, v___x_5445_, v___x_5447_, v___x_5449_, v_body_5416_);
v___x_5451_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5452_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5427_);
lean_ctor_set(v___x_5453_, 1, v___x_5452_);
v___x_5454_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5451_, v___x_5453_);
v___x_5455_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5431_, v___x_5454_);
v___x_5456_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5431_, v___x_5455_);
v___x_5457_ = l_Lean_Syntax_node4(v___x_5427_, v___x_5443_, v___x_5445_, v___x_5456_, v___x_5449_, v___y_5415_);
v___x_5458_ = l_Lean_Syntax_node2(v___x_5427_, v___x_5431_, v___x_5450_, v___x_5457_);
v___x_5459_ = l_Lean_Syntax_node1(v___x_5427_, v___x_5442_, v___x_5458_);
lean_inc_ref_n(v___x_5433_, 2);
v___x_5460_ = l_Lean_Syntax_node7(v___x_5427_, v___x_5428_, v___x_5430_, v___x_5433_, v___x_5433_, v___x_5433_, v___x_5439_, v___x_5441_, v___x_5459_);
v___x_5461_ = l_Lean_Elab_Do_elabDoElem(v___x_5460_, v_dec_5398_, v___x_5408_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
return v___x_5461_;
}
else
{
lean_object* v_ref_5462_; lean_object* v___x_5463_; lean_object* v_a_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
lean_dec(v_eq_x3f_5424_);
v_ref_5462_ = lean_ctor_get(v___y_5422_, 2);
v___x_5463_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5462_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc_n(v_a_5464_, 18);
lean_dec_ref(v___x_5463_);
v___x_5465_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__3));
v___x_5466_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__10));
v___x_5467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5467_, 0, v_a_5464_);
lean_ctor_set(v___x_5467_, 1, v___x_5466_);
v___x_5468_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5469_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5470_, 0, v_a_5464_);
lean_ctor_set(v___x_5470_, 1, v___x_5468_);
lean_ctor_set(v___x_5470_, 2, v___x_5469_);
v___x_5471_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__4));
lean_inc_ref_n(v___x_5470_, 3);
v___x_5472_ = l_Lean_Syntax_node2(v_a_5464_, v___x_5471_, v___x_5470_, v___y_5413_);
v___x_5473_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5468_, v___x_5472_);
v___x_5474_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__12));
v___x_5475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5475_, 0, v_a_5464_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
v___x_5476_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__5));
v___x_5477_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__6));
v___x_5478_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5479_, 0, v_a_5464_);
lean_ctor_set(v___x_5479_, 1, v___x_5478_);
v___x_5480_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5468_, v___y_5412_);
v___x_5481_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5468_, v___x_5480_);
v___x_5482_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__16));
v___x_5483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5483_, 0, v_a_5464_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
lean_inc_ref(v___x_5483_);
lean_inc_ref(v___x_5479_);
v___x_5484_ = l_Lean_Syntax_node4(v_a_5464_, v___x_5477_, v___x_5479_, v___x_5481_, v___x_5483_, v_body_5416_);
v___x_5485_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
v___x_5486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__21));
v___x_5487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5487_, 0, v_a_5464_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5485_, v___x_5487_);
v___x_5489_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5468_, v___x_5488_);
v___x_5490_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5468_, v___x_5489_);
v___x_5491_ = l_Lean_Syntax_node4(v_a_5464_, v___x_5477_, v___x_5479_, v___x_5490_, v___x_5483_, v___y_5415_);
v___x_5492_ = l_Lean_Syntax_node2(v_a_5464_, v___x_5468_, v___x_5484_, v___x_5491_);
v___x_5493_ = l_Lean_Syntax_node1(v_a_5464_, v___x_5476_, v___x_5492_);
v___x_5494_ = l_Lean_Syntax_node7(v_a_5464_, v___x_5465_, v___x_5467_, v___x_5470_, v___x_5470_, v___x_5470_, v___x_5473_, v___x_5475_, v___x_5493_);
v___x_5495_ = l_Lean_Elab_Do_elabDoElem(v___x_5494_, v_dec_5398_, v___x_5408_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
return v___x_5495_;
}
}
v___jp_5496_:
{
if (lean_obj_tag(v___y_5504_) == 0)
{
lean_dec_ref(v___y_5498_);
v___y_5411_ = v___y_5497_;
v___y_5412_ = v___y_5499_;
v___y_5413_ = v___y_5506_;
v___y_5414_ = v___y_5502_;
v___y_5415_ = v___y_5510_;
v_body_5416_ = v_a_5511_;
v___y_5417_ = v___y_5508_;
v___y_5418_ = v___y_5509_;
v___y_5419_ = v___y_5501_;
v___y_5420_ = v___y_5500_;
v___y_5421_ = v___y_5503_;
v___y_5422_ = v___y_5507_;
v___y_5423_ = v___y_5505_;
goto v___jp_5410_;
}
else
{
lean_dec_ref_known(v___y_5504_, 1);
if (v___x_5408_ == 0)
{
lean_dec_ref(v___y_5498_);
v___y_5411_ = v___y_5497_;
v___y_5412_ = v___y_5499_;
v___y_5413_ = v___y_5506_;
v___y_5414_ = v___y_5502_;
v___y_5415_ = v___y_5510_;
v_body_5416_ = v_a_5511_;
v___y_5417_ = v___y_5508_;
v___y_5418_ = v___y_5509_;
v___y_5419_ = v___y_5501_;
v___y_5420_ = v___y_5500_;
v___y_5421_ = v___y_5503_;
v___y_5422_ = v___y_5507_;
v___y_5423_ = v___y_5505_;
goto v___jp_5410_;
}
else
{
size_t v_sz_5512_; size_t v___x_5513_; lean_object* v___x_5514_; 
v_sz_5512_ = lean_array_size(v___y_5498_);
v___x_5513_ = ((size_t)0ULL);
v___x_5514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0(v___y_5498_, v_sz_5512_, v___x_5513_, v_a_5511_, v___y_5508_, v___y_5509_, v___y_5501_, v___y_5500_, v___y_5503_, v___y_5507_, v___y_5505_);
lean_dec_ref(v___y_5498_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref_known(v___x_5514_, 1);
v___y_5411_ = v___y_5497_;
v___y_5412_ = v___y_5499_;
v___y_5413_ = v___y_5506_;
v___y_5414_ = v___y_5502_;
v___y_5415_ = v___y_5510_;
v_body_5416_ = v_a_5515_;
v___y_5417_ = v___y_5508_;
v___y_5418_ = v___y_5509_;
v___y_5419_ = v___y_5501_;
v___y_5420_ = v___y_5500_;
v___y_5421_ = v___y_5503_;
v___y_5422_ = v___y_5507_;
v___y_5423_ = v___y_5505_;
goto v___jp_5410_;
}
else
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5523_; 
lean_dec(v___y_5510_);
lean_dec(v___y_5506_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5497_);
lean_dec_ref(v_dec_5398_);
v_a_5516_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5518_ = v___x_5514_;
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5514_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
}
}
v___jp_5524_:
{
lean_object* v___x_5538_; uint8_t v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5538_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__4));
v___x_5539_ = 0;
v___x_5540_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
v___x_5541_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v___y_5527_, v___y_5530_, v___x_5540_, v___y_5534_, v___y_5535_, v___y_5528_, v___y_5526_, v___y_5529_, v___y_5533_, v___y_5531_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5543_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref_known(v___x_5541_, 1);
v___x_5543_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_5542_, v___y_5526_, v___y_5529_, v___y_5533_, v___y_5531_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v___x_5544_; lean_object* v___x_5545_; 
lean_dec_ref_known(v___x_5543_, 1);
lean_inc(v___y_5530_);
v___x_5544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5544_, 0, v___y_5530_);
lean_ctor_set_uint8(v___x_5544_, sizeof(void*)*1, v___x_5539_);
lean_inc(v___y_5525_);
v___x_5545_ = l_Lean_Elab_Do_getPatternVarsEx(v___y_5525_, v___y_5535_, v___y_5528_, v___y_5526_, v___y_5529_, v___y_5533_, v___y_5531_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v___x_5547_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5546_);
lean_dec_ref_known(v___x_5545_, 1);
v___x_5547_ = l_Lean_Elab_Do_LetOrReassign_checkMutVars(v___x_5544_, v_a_5546_, v___y_5534_, v___y_5535_, v___y_5528_, v___y_5526_, v___y_5529_, v___y_5533_, v___y_5531_);
lean_dec_ref_known(v___x_5544_, 1);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_dec_ref_known(v___x_5547_, 1);
if (lean_obj_tag(v___y_5537_) == 0)
{
lean_object* v_toCold_5548_; lean_object* v_ref_5549_; lean_object* v___x_5550_; lean_object* v_a_5551_; lean_object* v_quotContext_5552_; lean_object* v_currMacroScope_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
v_toCold_5548_ = lean_ctor_get(v___y_5533_, 0);
v_ref_5549_ = lean_ctor_get(v___y_5533_, 2);
v___x_5550_ = l_Lean_Elab_Do_elabDoLetElse___lam__0(v_ref_5549_, v___y_5534_, v___y_5535_, v___y_5528_, v___y_5526_, v___y_5529_, v___y_5533_, v___y_5531_);
v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
lean_inc_n(v_a_5551_, 9);
lean_dec_ref(v___x_5550_);
v_quotContext_5552_ = lean_ctor_get(v_toCold_5548_, 8);
v_currMacroScope_5553_ = lean_ctor_get(v_toCold_5548_, 9);
v___x_5554_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5555_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__6));
v___x_5556_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__9));
v___x_5557_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl___closed__1));
v___x_5558_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__11, &l_Lean_Elab_Do_elabDoLetElse___closed__11_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__11);
v___x_5559_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__12));
lean_inc_n(v_currMacroScope_5553_, 2);
lean_inc_n(v_quotContext_5552_, 2);
v___x_5560_ = l_Lean_addMacroScope(v_quotContext_5552_, v___x_5559_, v_currMacroScope_5553_);
v___x_5561_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__16));
v___x_5562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5562_, 0, v_a_5551_);
lean_ctor_set(v___x_5562_, 1, v___x_5558_);
lean_ctor_set(v___x_5562_, 2, v___x_5560_);
lean_ctor_set(v___x_5562_, 3, v___x_5561_);
v___x_5563_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetElse___closed__18, &l_Lean_Elab_Do_elabDoLetElse___closed__18_once, _init_l_Lean_Elab_Do_elabDoLetElse___closed__18);
v___x_5564_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__21));
v___x_5565_ = l_Lean_addMacroScope(v_quotContext_5552_, v___x_5564_, v_currMacroScope_5553_);
v___x_5566_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__25));
v___x_5567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5567_, 0, v_a_5551_);
lean_ctor_set(v___x_5567_, 1, v___x_5563_);
lean_ctor_set(v___x_5567_, 2, v___x_5565_);
lean_ctor_set(v___x_5567_, 3, v___x_5566_);
v___x_5568_ = l_Lean_Syntax_node1(v_a_5551_, v___x_5554_, v___x_5567_);
v___x_5569_ = l_Lean_Syntax_node2(v_a_5551_, v___x_5557_, v___x_5562_, v___x_5568_);
v___x_5570_ = l_Lean_Syntax_node1(v_a_5551_, v___x_5556_, v___x_5569_);
v___x_5571_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_5572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5572_, 0, v_a_5551_);
lean_ctor_set(v___x_5572_, 1, v___x_5554_);
lean_ctor_set(v___x_5572_, 2, v___x_5571_);
v___x_5573_ = l_Lean_Syntax_node2(v_a_5551_, v___x_5555_, v___x_5570_, v___x_5572_);
v___x_5574_ = l_Lean_Syntax_node1(v_a_5551_, v___x_5554_, v___x_5573_);
v___x_5575_ = l_Lean_Syntax_node1(v_a_5551_, v___x_5538_, v___x_5574_);
v___y_5497_ = v_a_5542_;
v___y_5498_ = v_a_5546_;
v___y_5499_ = v___y_5525_;
v___y_5500_ = v___y_5526_;
v___y_5501_ = v___y_5528_;
v___y_5502_ = v___x_5539_;
v___y_5503_ = v___y_5529_;
v___y_5504_ = v___y_5530_;
v___y_5505_ = v___y_5531_;
v___y_5506_ = v___y_5532_;
v___y_5507_ = v___y_5533_;
v___y_5508_ = v___y_5534_;
v___y_5509_ = v___y_5535_;
v___y_5510_ = v___y_5536_;
v_a_5511_ = v___x_5575_;
goto v___jp_5496_;
}
else
{
lean_object* v_val_5576_; 
v_val_5576_ = lean_ctor_get(v___y_5537_, 0);
lean_inc(v_val_5576_);
lean_dec_ref_known(v___y_5537_, 1);
v___y_5497_ = v_a_5542_;
v___y_5498_ = v_a_5546_;
v___y_5499_ = v___y_5525_;
v___y_5500_ = v___y_5526_;
v___y_5501_ = v___y_5528_;
v___y_5502_ = v___x_5539_;
v___y_5503_ = v___y_5529_;
v___y_5504_ = v___y_5530_;
v___y_5505_ = v___y_5531_;
v___y_5506_ = v___y_5532_;
v___y_5507_ = v___y_5533_;
v___y_5508_ = v___y_5534_;
v___y_5509_ = v___y_5535_;
v___y_5510_ = v___y_5536_;
v_a_5511_ = v_val_5576_;
goto v___jp_5496_;
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec(v_a_5546_);
lean_dec(v_a_5542_);
lean_dec(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec(v___y_5532_);
lean_dec(v___y_5530_);
lean_dec(v___y_5525_);
lean_dec_ref(v_dec_5398_);
v_a_5577_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5547_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5547_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref_known(v___x_5544_, 1);
lean_dec(v_a_5542_);
lean_dec(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec(v___y_5532_);
lean_dec(v___y_5530_);
lean_dec(v___y_5525_);
lean_dec_ref(v_dec_5398_);
v_a_5585_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5545_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5545_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec(v_a_5542_);
lean_dec(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec(v___y_5532_);
lean_dec(v___y_5530_);
lean_dec(v___y_5525_);
lean_dec_ref(v_dec_5398_);
v_a_5593_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5543_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5543_);
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
else
{
lean_object* v_a_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
lean_dec(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec(v___y_5532_);
lean_dec(v___y_5530_);
lean_dec(v___y_5525_);
lean_dec_ref(v_dec_5398_);
v_a_5601_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5541_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_a_5601_);
lean_dec(v___x_5541_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5601_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
v___jp_5609_:
{
lean_object* v___x_5618_; lean_object* v_cfg_5619_; lean_object* v___x_5620_; uint8_t v___x_5621_; 
v___x_5618_ = lean_unsigned_to_nat(2u);
v_cfg_5619_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5618_);
v___x_5620_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_5619_);
v___x_5621_ = l_Lean_Syntax_isOfKind(v_cfg_5619_, v___x_5620_);
if (v___x_5621_ == 0)
{
lean_object* v___x_5622_; 
lean_dec(v_cfg_5619_);
lean_dec(v_mutTk_x3f_5610_);
lean_dec_ref(v_dec_5398_);
lean_dec(v_stx_5397_);
v___x_5622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5622_;
}
else
{
lean_object* v___x_5623_; lean_object* v_pattern_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5623_ = lean_unsigned_to_nat(3u);
v_pattern_5624_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5623_);
v___x_5625_ = lean_unsigned_to_nat(5u);
v___x_5626_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5625_);
v___x_5627_ = lean_unsigned_to_nat(7u);
v___x_5628_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5627_);
v___x_5629_ = lean_unsigned_to_nat(8u);
v___x_5630_ = l_Lean_Syntax_getArg(v_stx_5397_, v___x_5629_);
lean_dec(v_stx_5397_);
v___x_5631_ = l_Lean_Syntax_getOptional_x3f(v___x_5630_);
lean_dec(v___x_5630_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_object* v___x_5632_; 
v___x_5632_ = lean_box(0);
v___y_5525_ = v_pattern_5624_;
v___y_5526_ = v___y_5614_;
v___y_5527_ = v_cfg_5619_;
v___y_5528_ = v___y_5613_;
v___y_5529_ = v___y_5615_;
v___y_5530_ = v_mutTk_x3f_5610_;
v___y_5531_ = v___y_5617_;
v___y_5532_ = v___x_5626_;
v___y_5533_ = v___y_5616_;
v___y_5534_ = v___y_5611_;
v___y_5535_ = v___y_5612_;
v___y_5536_ = v___x_5628_;
v___y_5537_ = v___x_5632_;
goto v___jp_5524_;
}
else
{
lean_object* v_val_5633_; lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5640_; 
v_val_5633_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5635_ = v___x_5631_;
v_isShared_5636_ = v_isSharedCheck_5640_;
goto v_resetjp_5634_;
}
else
{
lean_inc(v_val_5633_);
lean_dec(v___x_5631_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5640_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5638_; 
if (v_isShared_5636_ == 0)
{
v___x_5638_ = v___x_5635_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_val_5633_);
v___x_5638_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
v___y_5525_ = v_pattern_5624_;
v___y_5526_ = v___y_5614_;
v___y_5527_ = v_cfg_5619_;
v___y_5528_ = v___y_5613_;
v___y_5529_ = v___y_5615_;
v___y_5530_ = v_mutTk_x3f_5610_;
v___y_5531_ = v___y_5617_;
v___y_5532_ = v___x_5626_;
v___y_5533_ = v___y_5616_;
v___y_5534_ = v___y_5611_;
v___y_5535_ = v___y_5612_;
v___y_5536_ = v___x_5628_;
v___y_5537_ = v___x_5638_;
goto v___jp_5524_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetElse___boxed(lean_object* v_stx_5650_, lean_object* v_dec_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Lean_Elab_Do_elabDoLetElse(v_stx_5650_, v_dec_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
lean_dec(v_a_5658_);
lean_dec_ref(v_a_5657_);
lean_dec(v_a_5656_);
lean_dec_ref(v_a_5655_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec_ref(v_a_5652_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(lean_object* v_as_5661_, size_t v_sz_5662_, size_t v_i_5663_, lean_object* v_b_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_){
_start:
{
lean_object* v___x_5673_; 
v___x_5673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___redArg(v_as_5661_, v_sz_5662_, v_i_5663_, v_b_5664_, v___y_5670_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0___boxed(lean_object* v_as_5674_, lean_object* v_sz_5675_, lean_object* v_i_5676_, lean_object* v_b_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
size_t v_sz_boxed_5686_; size_t v_i_boxed_5687_; lean_object* v_res_5688_; 
v_sz_boxed_5686_ = lean_unbox_usize(v_sz_5675_);
lean_dec(v_sz_5675_);
v_i_boxed_5687_ = lean_unbox_usize(v_i_5676_);
lean_dec(v_i_5676_);
v_res_5688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoLetElse_spec__0_spec__0(v_as_5674_, v_sz_boxed_5686_, v_i_boxed_5687_, v_b_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec_ref(v_as_5674_);
return v_res_5688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1(){
_start:
{
lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v___x_5696_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_5697_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__1));
v___x_5698_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___closed__1));
v___x_5699_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetElse___boxed), 10, 0);
v___x_5700_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5696_, v___x_5697_, v___x_5698_, v___x_5699_);
return v___x_5700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1___boxed(lean_object* v_a_5701_){
_start:
{
lean_object* v_res_5702_; 
v_res_5702_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetElse___regBuiltin_Lean_Elab_Do_elabDoLetElse__1();
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0(lean_object* v_otherwise_x3f_5703_, uint8_t v___x_5704_, lean_object* v___x_5705_, lean_object* v___x_5706_, lean_object* v___x_5707_, lean_object* v___x_5708_, lean_object* v___x_5709_, lean_object* v___x_5710_, lean_object* v_dec_5711_, uint8_t v___x_5712_, lean_object* v_mutTk_x3f_5713_, lean_object* v___x_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5703_) == 0)
{
lean_object* v_ref_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___y_5733_; 
lean_dec(v___y_5715_);
v_ref_5724_ = lean_ctor_get(v___y_5721_, 2);
v___x_5725_ = l_Lean_SourceInfo_fromRef(v_ref_5724_, v___x_5704_);
v___x_5726_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5707_);
lean_inc_ref(v___x_5706_);
lean_inc_ref(v___x_5705_);
v___x_5727_ = l_Lean_Name_mkStr4(v___x_5705_, v___x_5706_, v___x_5707_, v___x_5726_);
v___x_5728_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5725_);
v___x_5729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5725_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5731_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5713_) == 1)
{
lean_object* v_val_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; 
v_val_5748_ = lean_ctor_get(v_mutTk_x3f_5713_, 0);
v___x_5749_ = l_Lean_SourceInfo_fromRef(v_val_5748_, v___x_5712_);
v___x_5750_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5749_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
v___x_5752_ = l_Array_mkArray1___redArg(v___x_5751_);
v___y_5733_ = v___x_5752_;
goto v___jp_5732_;
}
else
{
lean_object* v___x_5753_; 
v___x_5753_ = lean_mk_empty_array_with_capacity(v___x_5714_);
v___y_5733_ = v___x_5753_;
goto v___jp_5732_;
}
v___jp_5732_:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5734_ = l_Array_append___redArg(v___x_5731_, v___y_5733_);
lean_dec_ref(v___y_5733_);
lean_inc_n(v___x_5725_, 6);
v___x_5735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5725_);
lean_ctor_set(v___x_5735_, 1, v___x_5730_);
lean_ctor_set(v___x_5735_, 2, v___x_5734_);
v___x_5736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5725_);
lean_ctor_set(v___x_5736_, 1, v___x_5730_);
lean_ctor_set(v___x_5736_, 2, v___x_5731_);
lean_inc_ref_n(v___x_5736_, 2);
v___x_5737_ = l_Lean_Syntax_node1(v___x_5725_, v___x_5708_, v___x_5736_);
v___x_5738_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5707_);
lean_inc_ref(v___x_5706_);
lean_inc_ref(v___x_5705_);
v___x_5739_ = l_Lean_Name_mkStr4(v___x_5705_, v___x_5706_, v___x_5707_, v___x_5738_);
v___x_5740_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5741_ = l_Lean_Name_mkStr4(v___x_5705_, v___x_5706_, v___x_5707_, v___x_5740_);
v___x_5742_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5725_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = l_Lean_Syntax_node5(v___x_5725_, v___x_5741_, v___x_5709_, v___x_5736_, v___x_5736_, v___x_5743_, v___x_5710_);
v___x_5745_ = l_Lean_Syntax_node1(v___x_5725_, v___x_5739_, v___x_5744_);
v___x_5746_ = l_Lean_Syntax_node4(v___x_5725_, v___x_5727_, v___x_5729_, v___x_5735_, v___x_5737_, v___x_5745_);
v___x_5747_ = l_Lean_Elab_Do_elabDoElem(v___x_5746_, v_dec_5711_, v___x_5712_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
return v___x_5747_;
}
}
else
{
lean_object* v_val_5754_; lean_object* v_ref_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___y_5764_; lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5785_; 
v_val_5754_ = lean_ctor_get(v_otherwise_x3f_5703_, 0);
lean_inc(v_val_5754_);
lean_dec_ref_known(v_otherwise_x3f_5703_, 1);
v_ref_5755_ = lean_ctor_get(v___y_5721_, 2);
v___x_5756_ = l_Lean_SourceInfo_fromRef(v_ref_5755_, v___x_5704_);
v___x_5757_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5758_ = l_Lean_Name_mkStr4(v___x_5705_, v___x_5706_, v___x_5707_, v___x_5757_);
v___x_5759_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5756_);
v___x_5760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5760_, 0, v___x_5756_);
lean_ctor_set(v___x_5760_, 1, v___x_5759_);
v___x_5761_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5762_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5713_) == 1)
{
lean_object* v_val_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; 
v_val_5798_ = lean_ctor_get(v_mutTk_x3f_5713_, 0);
v___x_5799_ = l_Lean_SourceInfo_fromRef(v_val_5798_, v___x_5712_);
v___x_5800_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5799_);
lean_ctor_set(v___x_5801_, 1, v___x_5800_);
v___x_5802_ = l_Array_mkArray1___redArg(v___x_5801_);
v___y_5785_ = v___x_5802_;
goto v___jp_5784_;
}
else
{
lean_object* v___x_5803_; 
v___x_5803_ = lean_mk_empty_array_with_capacity(v___x_5714_);
v___y_5785_ = v___x_5803_;
goto v___jp_5784_;
}
v___jp_5763_:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5769_ = l_Array_append___redArg(v___x_5762_, v___y_5768_);
lean_dec_ref(v___y_5768_);
lean_inc(v___x_5756_);
v___x_5770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5756_);
lean_ctor_set(v___x_5770_, 1, v___x_5761_);
lean_ctor_set(v___x_5770_, 2, v___x_5769_);
v___x_5771_ = lean_unsigned_to_nat(9u);
v___x_5772_ = lean_mk_empty_array_with_capacity(v___x_5771_);
v___x_5773_ = lean_array_push(v___x_5772_, v___x_5760_);
v___x_5774_ = lean_array_push(v___x_5773_, v___y_5765_);
v___x_5775_ = lean_array_push(v___x_5774_, v___y_5767_);
v___x_5776_ = lean_array_push(v___x_5775_, v___x_5709_);
v___x_5777_ = lean_array_push(v___x_5776_, v___y_5766_);
v___x_5778_ = lean_array_push(v___x_5777_, v___x_5710_);
v___x_5779_ = lean_array_push(v___x_5778_, v___y_5764_);
v___x_5780_ = lean_array_push(v___x_5779_, v_val_5754_);
v___x_5781_ = lean_array_push(v___x_5780_, v___x_5770_);
v___x_5782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5756_);
lean_ctor_set(v___x_5782_, 1, v___x_5758_);
lean_ctor_set(v___x_5782_, 2, v___x_5781_);
v___x_5783_ = l_Lean_Elab_Do_elabDoElem(v___x_5782_, v_dec_5711_, v___x_5712_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
return v___x_5783_;
}
v___jp_5784_:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___x_5786_ = l_Array_append___redArg(v___x_5762_, v___y_5785_);
lean_dec_ref(v___y_5785_);
lean_inc_n(v___x_5756_, 5);
v___x_5787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5756_);
lean_ctor_set(v___x_5787_, 1, v___x_5761_);
lean_ctor_set(v___x_5787_, 2, v___x_5786_);
v___x_5788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5788_, 0, v___x_5756_);
lean_ctor_set(v___x_5788_, 1, v___x_5761_);
lean_ctor_set(v___x_5788_, 2, v___x_5762_);
v___x_5789_ = l_Lean_Syntax_node1(v___x_5756_, v___x_5708_, v___x_5788_);
v___x_5790_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5756_);
lean_ctor_set(v___x_5791_, 1, v___x_5790_);
v___x_5792_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5756_);
lean_ctor_set(v___x_5793_, 1, v___x_5792_);
if (lean_obj_tag(v___y_5715_) == 0)
{
lean_object* v___x_5794_; 
v___x_5794_ = lean_mk_empty_array_with_capacity(v___x_5714_);
v___y_5764_ = v___x_5793_;
v___y_5765_ = v___x_5787_;
v___y_5766_ = v___x_5791_;
v___y_5767_ = v___x_5789_;
v___y_5768_ = v___x_5794_;
goto v___jp_5763_;
}
else
{
lean_object* v_val_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; 
v_val_5795_ = lean_ctor_get(v___y_5715_, 0);
lean_inc(v_val_5795_);
lean_dec_ref_known(v___y_5715_, 1);
v___x_5796_ = lean_mk_empty_array_with_capacity(v___x_5714_);
v___x_5797_ = lean_array_push(v___x_5796_, v_val_5795_);
v___y_5764_ = v___x_5793_;
v___y_5765_ = v___x_5787_;
v___y_5766_ = v___x_5791_;
v___y_5767_ = v___x_5789_;
v___y_5768_ = v___x_5797_;
goto v___jp_5763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5804_ = _args[0];
lean_object* v___x_5805_ = _args[1];
lean_object* v___x_5806_ = _args[2];
lean_object* v___x_5807_ = _args[3];
lean_object* v___x_5808_ = _args[4];
lean_object* v___x_5809_ = _args[5];
lean_object* v___x_5810_ = _args[6];
lean_object* v___x_5811_ = _args[7];
lean_object* v_dec_5812_ = _args[8];
lean_object* v___x_5813_ = _args[9];
lean_object* v_mutTk_x3f_5814_ = _args[10];
lean_object* v___x_5815_ = _args[11];
lean_object* v___y_5816_ = _args[12];
lean_object* v___y_5817_ = _args[13];
lean_object* v___y_5818_ = _args[14];
lean_object* v___y_5819_ = _args[15];
lean_object* v___y_5820_ = _args[16];
lean_object* v___y_5821_ = _args[17];
lean_object* v___y_5822_ = _args[18];
lean_object* v___y_5823_ = _args[19];
lean_object* v___y_5824_ = _args[20];
_start:
{
uint8_t v___x_22846__boxed_5825_; uint8_t v___x_22853__boxed_5826_; lean_object* v_res_5827_; 
v___x_22846__boxed_5825_ = lean_unbox(v___x_5805_);
v___x_22853__boxed_5826_ = lean_unbox(v___x_5813_);
v_res_5827_ = l_Lean_Elab_Do_elabDoLetArrow___lam__0(v_otherwise_x3f_5804_, v___x_22846__boxed_5825_, v___x_5806_, v___x_5807_, v___x_5808_, v___x_5809_, v___x_5810_, v___x_5811_, v_dec_5812_, v___x_22853__boxed_5826_, v_mutTk_x3f_5814_, v___x_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___x_5815_);
lean_dec(v_mutTk_x3f_5814_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1(lean_object* v_otherwise_x3f_5828_, uint8_t v___x_5829_, lean_object* v___x_5830_, lean_object* v___x_5831_, lean_object* v___x_5832_, lean_object* v___x_5833_, lean_object* v___x_5834_, lean_object* v___x_5835_, lean_object* v_dec_5836_, uint8_t v___x_5837_, lean_object* v_mutTk_x3f_5838_, lean_object* v___x_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
if (lean_obj_tag(v_otherwise_x3f_5828_) == 0)
{
lean_object* v_ref_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___y_5858_; 
lean_dec(v___y_5840_);
v_ref_5849_ = lean_ctor_get(v___y_5846_, 2);
v___x_5850_ = l_Lean_SourceInfo_fromRef(v_ref_5849_, v___x_5829_);
v___x_5851_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__0));
lean_inc_ref(v___x_5832_);
lean_inc_ref(v___x_5831_);
lean_inc_ref(v___x_5830_);
v___x_5852_ = l_Lean_Name_mkStr4(v___x_5830_, v___x_5831_, v___x_5832_, v___x_5851_);
v___x_5853_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5850_);
v___x_5854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5850_);
lean_ctor_set(v___x_5854_, 1, v___x_5853_);
v___x_5855_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5856_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5838_) == 1)
{
lean_object* v_val_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v_val_5873_ = lean_ctor_get(v_mutTk_x3f_5838_, 0);
v___x_5874_ = l_Lean_SourceInfo_fromRef(v_val_5873_, v___x_5837_);
v___x_5875_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5874_);
lean_ctor_set(v___x_5876_, 1, v___x_5875_);
v___x_5877_ = l_Array_mkArray1___redArg(v___x_5876_);
v___y_5858_ = v___x_5877_;
goto v___jp_5857_;
}
else
{
lean_object* v___x_5878_; 
v___x_5878_ = lean_mk_empty_array_with_capacity(v___x_5839_);
v___y_5858_ = v___x_5878_;
goto v___jp_5857_;
}
v___jp_5857_:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5859_ = l_Array_append___redArg(v___x_5856_, v___y_5858_);
lean_dec_ref(v___y_5858_);
lean_inc_n(v___x_5850_, 6);
v___x_5860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5850_);
lean_ctor_set(v___x_5860_, 1, v___x_5855_);
lean_ctor_set(v___x_5860_, 2, v___x_5859_);
v___x_5861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5850_);
lean_ctor_set(v___x_5861_, 1, v___x_5855_);
lean_ctor_set(v___x_5861_, 2, v___x_5856_);
lean_inc_ref_n(v___x_5861_, 2);
v___x_5862_ = l_Lean_Syntax_node1(v___x_5850_, v___x_5833_, v___x_5861_);
v___x_5863_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__3));
lean_inc_ref(v___x_5832_);
lean_inc_ref(v___x_5831_);
lean_inc_ref(v___x_5830_);
v___x_5864_ = l_Lean_Name_mkStr4(v___x_5830_, v___x_5831_, v___x_5832_, v___x_5863_);
v___x_5865_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__9));
v___x_5866_ = l_Lean_Name_mkStr4(v___x_5830_, v___x_5831_, v___x_5832_, v___x_5865_);
v___x_5867_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5850_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = l_Lean_Syntax_node5(v___x_5850_, v___x_5866_, v___x_5834_, v___x_5861_, v___x_5861_, v___x_5868_, v___x_5835_);
v___x_5870_ = l_Lean_Syntax_node1(v___x_5850_, v___x_5864_, v___x_5869_);
v___x_5871_ = l_Lean_Syntax_node4(v___x_5850_, v___x_5852_, v___x_5854_, v___x_5860_, v___x_5862_, v___x_5870_);
v___x_5872_ = l_Lean_Elab_Do_elabDoElem(v___x_5871_, v_dec_5836_, v___x_5837_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
return v___x_5872_;
}
}
else
{
lean_object* v_val_5879_; lean_object* v_ref_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___y_5889_; lean_object* v___y_5890_; lean_object* v___y_5891_; lean_object* v___y_5892_; lean_object* v___y_5893_; lean_object* v___y_5910_; 
v_val_5879_ = lean_ctor_get(v_otherwise_x3f_5828_, 0);
lean_inc(v_val_5879_);
lean_dec_ref_known(v_otherwise_x3f_5828_, 1);
v_ref_5880_ = lean_ctor_get(v___y_5846_, 2);
v___x_5881_ = l_Lean_SourceInfo_fromRef(v_ref_5880_, v___x_5829_);
v___x_5882_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__0));
v___x_5883_ = l_Lean_Name_mkStr4(v___x_5830_, v___x_5831_, v___x_5832_, v___x_5882_);
v___x_5884_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__1___closed__6));
lean_inc(v___x_5881_);
v___x_5885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5885_, 0, v___x_5881_);
lean_ctor_set(v___x_5885_, 1, v___x_5884_);
v___x_5886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_5887_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
if (lean_obj_tag(v_mutTk_x3f_5838_) == 1)
{
lean_object* v_val_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v_val_5923_ = lean_ctor_get(v_mutTk_x3f_5838_, 0);
v___x_5924_ = l_Lean_SourceInfo_fromRef(v_val_5923_, v___x_5837_);
v___x_5925_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__11));
v___x_5926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5924_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = l_Array_mkArray1___redArg(v___x_5926_);
v___y_5910_ = v___x_5927_;
goto v___jp_5909_;
}
else
{
lean_object* v___x_5928_; 
v___x_5928_ = lean_mk_empty_array_with_capacity(v___x_5839_);
v___y_5910_ = v___x_5928_;
goto v___jp_5909_;
}
v___jp_5888_:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5894_ = l_Array_append___redArg(v___x_5887_, v___y_5893_);
lean_dec_ref(v___y_5893_);
lean_inc(v___x_5881_);
v___x_5895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5881_);
lean_ctor_set(v___x_5895_, 1, v___x_5886_);
lean_ctor_set(v___x_5895_, 2, v___x_5894_);
v___x_5896_ = lean_unsigned_to_nat(9u);
v___x_5897_ = lean_mk_empty_array_with_capacity(v___x_5896_);
v___x_5898_ = lean_array_push(v___x_5897_, v___x_5885_);
v___x_5899_ = lean_array_push(v___x_5898_, v___y_5891_);
v___x_5900_ = lean_array_push(v___x_5899_, v___y_5890_);
v___x_5901_ = lean_array_push(v___x_5900_, v___x_5834_);
v___x_5902_ = lean_array_push(v___x_5901_, v___y_5892_);
v___x_5903_ = lean_array_push(v___x_5902_, v___x_5835_);
v___x_5904_ = lean_array_push(v___x_5903_, v___y_5889_);
v___x_5905_ = lean_array_push(v___x_5904_, v_val_5879_);
v___x_5906_ = lean_array_push(v___x_5905_, v___x_5895_);
v___x_5907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5881_);
lean_ctor_set(v___x_5907_, 1, v___x_5883_);
lean_ctor_set(v___x_5907_, 2, v___x_5906_);
v___x_5908_ = l_Lean_Elab_Do_elabDoElem(v___x_5907_, v_dec_5836_, v___x_5837_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
return v___x_5908_;
}
v___jp_5909_:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v___x_5911_ = l_Array_append___redArg(v___x_5887_, v___y_5910_);
lean_dec_ref(v___y_5910_);
lean_inc_n(v___x_5881_, 5);
v___x_5912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5881_);
lean_ctor_set(v___x_5912_, 1, v___x_5886_);
lean_ctor_set(v___x_5912_, 2, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5881_);
lean_ctor_set(v___x_5913_, 1, v___x_5886_);
lean_ctor_set(v___x_5913_, 2, v___x_5887_);
v___x_5914_ = l_Lean_Syntax_node1(v___x_5881_, v___x_5833_, v___x_5913_);
v___x_5915_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_5916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5881_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetOrReassign___lam__6___closed__15));
v___x_5918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5881_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
if (lean_obj_tag(v___y_5840_) == 0)
{
lean_object* v___x_5919_; 
v___x_5919_ = lean_mk_empty_array_with_capacity(v___x_5839_);
v___y_5889_ = v___x_5918_;
v___y_5890_ = v___x_5914_;
v___y_5891_ = v___x_5912_;
v___y_5892_ = v___x_5916_;
v___y_5893_ = v___x_5919_;
goto v___jp_5888_;
}
else
{
lean_object* v_val_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v_val_5920_ = lean_ctor_get(v___y_5840_, 0);
lean_inc(v_val_5920_);
lean_dec_ref_known(v___y_5840_, 1);
v___x_5921_ = lean_mk_empty_array_with_capacity(v___x_5839_);
v___x_5922_ = lean_array_push(v___x_5921_, v_val_5920_);
v___y_5889_ = v___x_5918_;
v___y_5890_ = v___x_5914_;
v___y_5891_ = v___x_5912_;
v___y_5892_ = v___x_5916_;
v___y_5893_ = v___x_5922_;
goto v___jp_5888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed(lean_object** _args){
lean_object* v_otherwise_x3f_5929_ = _args[0];
lean_object* v___x_5930_ = _args[1];
lean_object* v___x_5931_ = _args[2];
lean_object* v___x_5932_ = _args[3];
lean_object* v___x_5933_ = _args[4];
lean_object* v___x_5934_ = _args[5];
lean_object* v___x_5935_ = _args[6];
lean_object* v___x_5936_ = _args[7];
lean_object* v_dec_5937_ = _args[8];
lean_object* v___x_5938_ = _args[9];
lean_object* v_mutTk_x3f_5939_ = _args[10];
lean_object* v___x_5940_ = _args[11];
lean_object* v___y_5941_ = _args[12];
lean_object* v___y_5942_ = _args[13];
lean_object* v___y_5943_ = _args[14];
lean_object* v___y_5944_ = _args[15];
lean_object* v___y_5945_ = _args[16];
lean_object* v___y_5946_ = _args[17];
lean_object* v___y_5947_ = _args[18];
lean_object* v___y_5948_ = _args[19];
lean_object* v___y_5949_ = _args[20];
_start:
{
uint8_t v___x_23077__boxed_5950_; uint8_t v___x_23084__boxed_5951_; lean_object* v_res_5952_; 
v___x_23077__boxed_5950_ = lean_unbox(v___x_5930_);
v___x_23084__boxed_5951_ = lean_unbox(v___x_5938_);
v_res_5952_ = l_Lean_Elab_Do_elabDoLetArrow___lam__1(v_otherwise_x3f_5929_, v___x_23077__boxed_5950_, v___x_5931_, v___x_5932_, v___x_5933_, v___x_5934_, v___x_5935_, v___x_5936_, v_dec_5937_, v___x_23084__boxed_5951_, v_mutTk_x3f_5939_, v___x_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec(v___y_5946_);
lean_dec_ref(v___y_5945_);
lean_dec(v___y_5944_);
lean_dec_ref(v___y_5943_);
lean_dec_ref(v___y_5942_);
lean_dec(v___x_5940_);
lean_dec(v_mutTk_x3f_5939_);
return v_res_5952_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5954_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__0));
v___x_5955_ = l_Lean_stringToMessageData(v___x_5954_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow(lean_object* v_stx_5962_, lean_object* v_dec_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_){
_start:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; uint8_t v___x_5976_; 
v___x_5972_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__0));
v___x_5973_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__1));
v___x_5974_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__2));
v___x_5975_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
lean_inc(v_stx_5962_);
v___x_5976_ = l_Lean_Syntax_isOfKind(v_stx_5962_, v___x_5975_);
if (v___x_5976_ == 0)
{
lean_object* v___x_5977_; 
lean_dec_ref(v_dec_5963_);
lean_dec(v_stx_5962_);
v___x_5977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_5977_;
}
else
{
lean_object* v___x_5978_; lean_object* v___y_5980_; uint8_t v___y_5981_; lean_object* v___y_5982_; lean_object* v___y_5983_; lean_object* v___y_5984_; lean_object* v___y_5985_; lean_object* v___y_5986_; lean_object* v___y_5987_; lean_object* v___y_5988_; lean_object* v___y_5989_; lean_object* v___y_5990_; lean_object* v___y_5991_; lean_object* v___y_5992_; lean_object* v___y_5993_; uint8_t v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; uint8_t v___y_6015_; lean_object* v___y_6016_; lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6019_; lean_object* v___y_6020_; lean_object* v___y_6021_; lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; uint8_t v___y_6025_; lean_object* v___y_6026_; lean_object* v___y_6027_; lean_object* v___y_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___y_6031_; lean_object* v___y_6034_; lean_object* v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6039_; lean_object* v___y_6040_; lean_object* v___y_6041_; uint8_t v___y_6042_; lean_object* v___y_6043_; uint8_t v___y_6044_; lean_object* v___y_6045_; lean_object* v___y_6046_; lean_object* v___y_6047_; lean_object* v___y_6048_; lean_object* v___y_6049_; lean_object* v___y_6050_; lean_object* v___y_6069_; lean_object* v___y_6070_; uint8_t v___y_6071_; lean_object* v___y_6072_; lean_object* v___y_6073_; lean_object* v___y_6074_; lean_object* v___y_6075_; lean_object* v___y_6076_; lean_object* v___y_6077_; lean_object* v___y_6078_; lean_object* v___y_6079_; lean_object* v___y_6080_; uint8_t v___y_6081_; lean_object* v___y_6082_; lean_object* v___y_6083_; lean_object* v___y_6084_; lean_object* v___y_6085_; lean_object* v_tk_6087_; lean_object* v___x_6088_; uint8_t v___y_6090_; lean_object* v___y_6091_; lean_object* v___y_6092_; lean_object* v___y_6093_; lean_object* v___y_6094_; uint8_t v___y_6095_; lean_object* v___y_6096_; lean_object* v___y_6097_; lean_object* v___y_6098_; lean_object* v___y_6099_; lean_object* v___y_6100_; lean_object* v_patType_x3f_6101_; lean_object* v___y_6102_; lean_object* v___y_6103_; lean_object* v___y_6104_; lean_object* v___y_6105_; lean_object* v___y_6106_; lean_object* v___y_6107_; lean_object* v___y_6108_; lean_object* v___y_6153_; lean_object* v___y_6154_; uint8_t v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; uint8_t v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v_patType_x3f_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6170_; lean_object* v___y_6189_; uint8_t v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v___y_6193_; lean_object* v_xType_x3f_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v___y_6230_; lean_object* v___y_6231_; lean_object* v___y_6232_; uint8_t v___y_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; lean_object* v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___y_6240_; lean_object* v___y_6241_; lean_object* v___y_6242_; lean_object* v___y_6243_; lean_object* v___y_6244_; lean_object* v___y_6245_; lean_object* v___y_6246_; lean_object* v___y_6289_; lean_object* v___y_6290_; lean_object* v___y_6291_; lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v___y_6300_; uint8_t v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6303_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; lean_object* v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; uint8_t v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; uint8_t v___y_6337_; lean_object* v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6351_; uint8_t v___y_6352_; lean_object* v___y_6353_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___y_6357_; lean_object* v___y_6358_; uint8_t v___y_6359_; lean_object* v_mutTk_x3f_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; lean_object* v___x_6403_; uint8_t v___x_6404_; 
v___x_5978_ = lean_unsigned_to_nat(0u);
v_tk_6087_ = l_Lean_Syntax_getArg(v_stx_5962_, v___x_5978_);
v___x_6088_ = lean_unsigned_to_nat(1u);
v___x_6403_ = l_Lean_Syntax_getArg(v_stx_5962_, v___x_6088_);
v___x_6404_ = l_Lean_Syntax_isNone(v___x_6403_);
if (v___x_6404_ == 0)
{
uint8_t v___x_6405_; 
lean_inc(v___x_6403_);
v___x_6405_ = l_Lean_Syntax_matchesNull(v___x_6403_, v___x_6088_);
if (v___x_6405_ == 0)
{
lean_object* v___x_6406_; 
lean_dec(v___x_6403_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
lean_dec(v_stx_5962_);
v___x_6406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6406_;
}
else
{
lean_object* v_mutTk_x3f_6407_; lean_object* v___x_6408_; 
v_mutTk_x3f_6407_ = l_Lean_Syntax_getArg(v___x_6403_, v___x_5978_);
lean_dec(v___x_6403_);
v___x_6408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6408_, 0, v_mutTk_x3f_6407_);
v_mutTk_x3f_6362_ = v___x_6408_;
v___y_6363_ = v_a_5964_;
v___y_6364_ = v_a_5965_;
v___y_6365_ = v_a_5966_;
v___y_6366_ = v_a_5967_;
v___y_6367_ = v_a_5968_;
v___y_6368_ = v_a_5969_;
v___y_6369_ = v_a_5970_;
goto v___jp_6361_;
}
}
else
{
lean_object* v___x_6409_; 
lean_dec(v___x_6403_);
v___x_6409_ = lean_box(0);
v_mutTk_x3f_6362_ = v___x_6409_;
v___y_6363_ = v_a_5964_;
v___y_6364_ = v_a_5965_;
v___y_6365_ = v_a_5966_;
v___y_6366_ = v_a_5967_;
v___y_6367_ = v_a_5968_;
v___y_6368_ = v_a_5969_;
v___y_6369_ = v_a_5970_;
goto v___jp_6361_;
}
v___jp_5979_:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___x_5997_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_5998_ = l_Lean_Core_mkFreshUserName(v___x_5997_, v___y_5989_, v___y_5982_);
if (lean_obj_tag(v___x_5998_) == 0)
{
lean_object* v_a_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___y_6003_; uint8_t v___x_6004_; lean_object* v___x_6005_; 
v_a_5999_ = lean_ctor_get(v___x_5998_, 0);
lean_inc(v_a_5999_);
lean_dec_ref_known(v___x_5998_, 1);
v___x_6000_ = l_Lean_mkIdentFrom(v___y_5980_, v_a_5999_, v___y_5994_);
lean_dec(v___y_5980_);
v___x_6001_ = lean_box(v___y_5981_);
v___x_6002_ = lean_box(v___x_5976_);
lean_inc(v___x_6000_);
lean_inc(v___y_5984_);
v___y_6003_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__1___boxed), 21, 13);
lean_closure_set(v___y_6003_, 0, v___y_5983_);
lean_closure_set(v___y_6003_, 1, v___x_6001_);
lean_closure_set(v___y_6003_, 2, v___x_5972_);
lean_closure_set(v___y_6003_, 3, v___x_5973_);
lean_closure_set(v___y_6003_, 4, v___x_5974_);
lean_closure_set(v___y_6003_, 5, v___y_5984_);
lean_closure_set(v___y_6003_, 6, v___y_5995_);
lean_closure_set(v___y_6003_, 7, v___x_6000_);
lean_closure_set(v___y_6003_, 8, v_dec_5963_);
lean_closure_set(v___y_6003_, 9, v___x_6002_);
lean_closure_set(v___y_6003_, 10, v___y_5987_);
lean_closure_set(v___y_6003_, 11, v___x_5978_);
lean_closure_set(v___y_6003_, 12, v___y_5996_);
v___x_6004_ = 0;
v___x_6005_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6000_, v___y_5985_, v___y_5988_, v___y_6003_, v___x_6004_, v___y_5992_, v___y_5990_, v___y_5991_, v___y_5993_, v___y_5986_, v___y_5989_, v___y_5982_);
return v___x_6005_;
}
else
{
lean_object* v_a_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6013_; 
lean_dec(v___y_5996_);
lean_dec(v___y_5995_);
lean_dec(v___y_5988_);
lean_dec(v___y_5987_);
lean_dec(v___y_5985_);
lean_dec(v___y_5983_);
lean_dec(v___y_5980_);
lean_dec_ref(v_dec_5963_);
v_a_6006_ = lean_ctor_get(v___x_5998_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_5998_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6008_ = v___x_5998_;
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_a_6006_);
lean_dec(v___x_5998_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
if (v_isShared_6009_ == 0)
{
v___x_6011_ = v___x_6008_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_a_6006_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
}
v___jp_6014_:
{
lean_object* v___x_6032_; 
v___x_6032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6032_, 0, v___y_6026_);
v___y_5980_ = v___y_6030_;
v___y_5981_ = v___y_6015_;
v___y_5982_ = v___y_6027_;
v___y_5983_ = v___x_6032_;
v___y_5984_ = v___y_6016_;
v___y_5985_ = v___y_6019_;
v___y_5986_ = v___y_6023_;
v___y_5987_ = v___y_6017_;
v___y_5988_ = v___y_6024_;
v___y_5989_ = v___y_6028_;
v___y_5990_ = v___y_6022_;
v___y_5991_ = v___y_6021_;
v___y_5992_ = v___y_6020_;
v___y_5993_ = v___y_6029_;
v___y_5994_ = v___y_6025_;
v___y_5995_ = v___y_6018_;
v___y_5996_ = v___y_6031_;
goto v___jp_5979_;
}
v___jp_6033_:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; 
v___x_6051_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6052_ = l_Lean_Core_mkFreshUserName(v___x_6051_, v___y_6046_, v___y_6038_);
if (lean_obj_tag(v___x_6052_) == 0)
{
lean_object* v_a_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___y_6057_; uint8_t v___x_6058_; lean_object* v___x_6059_; 
v_a_6053_ = lean_ctor_get(v___x_6052_, 0);
lean_inc(v_a_6053_);
lean_dec_ref_known(v___x_6052_, 1);
v___x_6054_ = l_Lean_mkIdentFrom(v___y_6040_, v_a_6053_, v___y_6042_);
lean_dec(v___y_6040_);
v___x_6055_ = lean_box(v___y_6044_);
v___x_6056_ = lean_box(v___x_5976_);
lean_inc(v___x_6054_);
lean_inc(v___y_6037_);
v___y_6057_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___lam__0___boxed), 21, 13);
lean_closure_set(v___y_6057_, 0, v___y_6041_);
lean_closure_set(v___y_6057_, 1, v___x_6055_);
lean_closure_set(v___y_6057_, 2, v___x_5972_);
lean_closure_set(v___y_6057_, 3, v___x_5973_);
lean_closure_set(v___y_6057_, 4, v___x_5974_);
lean_closure_set(v___y_6057_, 5, v___y_6037_);
lean_closure_set(v___y_6057_, 6, v___y_6048_);
lean_closure_set(v___y_6057_, 7, v___x_6054_);
lean_closure_set(v___y_6057_, 8, v_dec_5963_);
lean_closure_set(v___y_6057_, 9, v___x_6056_);
lean_closure_set(v___y_6057_, 10, v___y_6039_);
lean_closure_set(v___y_6057_, 11, v___x_5978_);
lean_closure_set(v___y_6057_, 12, v___y_6050_);
v___x_6058_ = 0;
v___x_6059_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6054_, v___y_6047_, v___y_6045_, v___y_6057_, v___x_6058_, v___y_6036_, v___y_6043_, v___y_6049_, v___y_6034_, v___y_6035_, v___y_6046_, v___y_6038_);
return v___x_6059_;
}
else
{
lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
lean_dec(v___y_6050_);
lean_dec(v___y_6048_);
lean_dec(v___y_6047_);
lean_dec(v___y_6045_);
lean_dec(v___y_6041_);
lean_dec(v___y_6040_);
lean_dec(v___y_6039_);
lean_dec_ref(v_dec_5963_);
v_a_6060_ = lean_ctor_get(v___x_6052_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6052_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6062_ = v___x_6052_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_dec(v___x_6052_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
}
v___jp_6068_:
{
lean_object* v___x_6086_; 
v___x_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6086_, 0, v___y_6074_);
v___y_6034_ = v___y_6076_;
v___y_6035_ = v___y_6080_;
v___y_6036_ = v___y_6084_;
v___y_6037_ = v___y_6069_;
v___y_6038_ = v___y_6075_;
v___y_6039_ = v___y_6070_;
v___y_6040_ = v___y_6083_;
v___y_6041_ = v___x_6086_;
v___y_6042_ = v___y_6081_;
v___y_6043_ = v___y_6077_;
v___y_6044_ = v___y_6071_;
v___y_6045_ = v___y_6082_;
v___y_6046_ = v___y_6078_;
v___y_6047_ = v___y_6079_;
v___y_6048_ = v___y_6072_;
v___y_6049_ = v___y_6073_;
v___y_6050_ = v___y_6085_;
goto v___jp_6033_;
}
v___jp_6089_:
{
lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; uint8_t v___x_6112_; 
v___x_6109_ = l_Lean_Syntax_getArg(v___y_6094_, v___y_6100_);
v___x_6110_ = lean_unsigned_to_nat(4u);
v___x_6111_ = l_Lean_Syntax_getArg(v___y_6094_, v___x_6110_);
lean_dec(v___y_6094_);
lean_inc(v___x_6111_);
v___x_6112_ = l_Lean_Syntax_matchesNull(v___x_6111_, v___x_5978_);
if (v___x_6112_ == 0)
{
uint8_t v___x_6113_; 
lean_dec(v___y_6099_);
lean_dec(v_tk_6087_);
v___x_6113_ = l_Lean_Syntax_isNone(v___x_6111_);
if (v___x_6113_ == 0)
{
uint8_t v___x_6114_; 
lean_inc(v___x_6111_);
v___x_6114_ = l_Lean_Syntax_matchesNull(v___x_6111_, v___y_6100_);
if (v___x_6114_ == 0)
{
lean_object* v___x_6115_; 
lean_dec(v___x_6111_);
lean_dec(v___x_6109_);
lean_dec(v_patType_x3f_6101_);
lean_dec(v___y_6098_);
lean_dec(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec_ref(v_dec_5963_);
v___x_6115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6115_;
}
else
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6116_ = l_Lean_Syntax_getArg(v___x_6111_, v___x_6088_);
v___x_6117_ = l_Lean_Syntax_getArg(v___x_6111_, v___y_6097_);
lean_dec(v___x_6111_);
v___x_6118_ = l_Lean_Syntax_getOptional_x3f(v___x_6117_);
lean_dec(v___x_6117_);
if (lean_obj_tag(v___x_6118_) == 0)
{
lean_inc(v___y_6096_);
v___y_6015_ = v___y_6090_;
v___y_6016_ = v___y_6091_;
v___y_6017_ = v___y_6092_;
v___y_6018_ = v___y_6093_;
v___y_6019_ = v_patType_x3f_6101_;
v___y_6020_ = v___y_6102_;
v___y_6021_ = v___y_6104_;
v___y_6022_ = v___y_6103_;
v___y_6023_ = v___y_6106_;
v___y_6024_ = v___x_6109_;
v___y_6025_ = v___y_6095_;
v___y_6026_ = v___x_6116_;
v___y_6027_ = v___y_6108_;
v___y_6028_ = v___y_6107_;
v___y_6029_ = v___y_6105_;
v___y_6030_ = v___y_6098_;
v___y_6031_ = v___y_6096_;
goto v___jp_6014_;
}
else
{
lean_object* v_val_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6126_; 
v_val_6119_ = lean_ctor_get(v___x_6118_, 0);
v_isSharedCheck_6126_ = !lean_is_exclusive(v___x_6118_);
if (v_isSharedCheck_6126_ == 0)
{
v___x_6121_ = v___x_6118_;
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_val_6119_);
lean_dec(v___x_6118_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6124_; 
if (v_isShared_6122_ == 0)
{
v___x_6124_ = v___x_6121_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_val_6119_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
v___y_6015_ = v___y_6090_;
v___y_6016_ = v___y_6091_;
v___y_6017_ = v___y_6092_;
v___y_6018_ = v___y_6093_;
v___y_6019_ = v_patType_x3f_6101_;
v___y_6020_ = v___y_6102_;
v___y_6021_ = v___y_6104_;
v___y_6022_ = v___y_6103_;
v___y_6023_ = v___y_6106_;
v___y_6024_ = v___x_6109_;
v___y_6025_ = v___y_6095_;
v___y_6026_ = v___x_6116_;
v___y_6027_ = v___y_6108_;
v___y_6028_ = v___y_6107_;
v___y_6029_ = v___y_6105_;
v___y_6030_ = v___y_6098_;
v___y_6031_ = v___x_6124_;
goto v___jp_6014_;
}
}
}
}
}
else
{
lean_dec(v___x_6111_);
lean_inc_n(v___y_6096_, 2);
v___y_5980_ = v___y_6098_;
v___y_5981_ = v___y_6090_;
v___y_5982_ = v___y_6108_;
v___y_5983_ = v___y_6096_;
v___y_5984_ = v___y_6091_;
v___y_5985_ = v_patType_x3f_6101_;
v___y_5986_ = v___y_6106_;
v___y_5987_ = v___y_6092_;
v___y_5988_ = v___x_6109_;
v___y_5989_ = v___y_6107_;
v___y_5990_ = v___y_6103_;
v___y_5991_ = v___y_6104_;
v___y_5992_ = v___y_6102_;
v___y_5993_ = v___y_6105_;
v___y_5994_ = v___y_6095_;
v___y_5995_ = v___y_6093_;
v___y_5996_ = v___y_6096_;
goto v___jp_5979_;
}
}
else
{
lean_object* v___x_6127_; lean_object* v___x_6128_; 
lean_dec(v___x_6111_);
lean_dec(v___y_6098_);
lean_dec(v___y_6093_);
lean_dec(v___y_6092_);
v___x_6127_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6128_ = l_Lean_Core_mkFreshUserName(v___x_6127_, v___y_6107_, v___y_6108_);
if (lean_obj_tag(v___x_6128_) == 0)
{
lean_object* v_a_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v_a_6129_ = lean_ctor_get(v___x_6128_, 0);
lean_inc(v_a_6129_);
lean_dec_ref_known(v___x_6128_, 1);
v___x_6130_ = l_Lean_mkIdentFrom(v___y_6099_, v_a_6129_, v___y_6095_);
lean_dec(v___y_6099_);
v___x_6131_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5963_, v_tk_6087_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_);
lean_dec(v_tk_6087_);
if (lean_obj_tag(v___x_6131_) == 0)
{
lean_object* v_a_6132_; uint8_t v_kind_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v_a_6132_ = lean_ctor_get(v___x_6131_, 0);
lean_inc(v_a_6132_);
lean_dec_ref_known(v___x_6131_, 1);
v_kind_6133_ = lean_ctor_get_uint8(v_a_6132_, sizeof(void*)*3);
v___x_6134_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6134_, 0, v_a_6132_);
v___x_6135_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6130_, v_patType_x3f_6101_, v___x_6109_, v___x_6134_, v_kind_6133_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_);
return v___x_6135_;
}
else
{
lean_object* v_a_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6143_; 
lean_dec(v___x_6130_);
lean_dec(v___x_6109_);
lean_dec(v_patType_x3f_6101_);
v_a_6136_ = lean_ctor_get(v___x_6131_, 0);
v_isSharedCheck_6143_ = !lean_is_exclusive(v___x_6131_);
if (v_isSharedCheck_6143_ == 0)
{
v___x_6138_ = v___x_6131_;
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_a_6136_);
lean_dec(v___x_6131_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v___x_6141_; 
if (v_isShared_6139_ == 0)
{
v___x_6141_ = v___x_6138_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
v___x_6141_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
return v___x_6141_;
}
}
}
}
else
{
lean_object* v_a_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6151_; 
lean_dec(v___x_6109_);
lean_dec(v_patType_x3f_6101_);
lean_dec(v___y_6099_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v_a_6144_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6151_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6151_ == 0)
{
v___x_6146_ = v___x_6128_;
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_a_6144_);
lean_dec(v___x_6128_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6149_; 
if (v_isShared_6147_ == 0)
{
v___x_6149_ = v___x_6146_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6150_; 
v_reuseFailAlloc_6150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_a_6144_);
v___x_6149_ = v_reuseFailAlloc_6150_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
return v___x_6149_;
}
}
}
}
}
v___jp_6152_:
{
lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; uint8_t v___x_6174_; 
v___x_6171_ = l_Lean_Syntax_getArg(v___y_6157_, v___y_6162_);
v___x_6172_ = lean_unsigned_to_nat(4u);
v___x_6173_ = l_Lean_Syntax_getArg(v___y_6157_, v___x_6172_);
lean_dec(v___y_6157_);
v___x_6174_ = l_Lean_Syntax_isNone(v___x_6173_);
if (v___x_6174_ == 0)
{
uint8_t v___x_6175_; 
lean_inc(v___x_6173_);
v___x_6175_ = l_Lean_Syntax_matchesNull(v___x_6173_, v___y_6162_);
if (v___x_6175_ == 0)
{
lean_object* v___x_6176_; 
lean_dec(v___x_6173_);
lean_dec(v___x_6171_);
lean_dec(v_patType_x3f_6163_);
lean_dec(v___y_6161_);
lean_dec(v___y_6156_);
lean_dec(v___y_6154_);
lean_dec_ref(v_dec_5963_);
v___x_6176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6176_;
}
else
{
lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6177_ = l_Lean_Syntax_getArg(v___x_6173_, v___x_6088_);
v___x_6178_ = l_Lean_Syntax_getArg(v___x_6173_, v___y_6160_);
lean_dec(v___x_6173_);
v___x_6179_ = l_Lean_Syntax_getOptional_x3f(v___x_6178_);
lean_dec(v___x_6178_);
if (lean_obj_tag(v___x_6179_) == 0)
{
lean_inc(v___y_6159_);
v___y_6069_ = v___y_6153_;
v___y_6070_ = v___y_6154_;
v___y_6071_ = v___y_6155_;
v___y_6072_ = v___y_6156_;
v___y_6073_ = v___y_6166_;
v___y_6074_ = v___x_6177_;
v___y_6075_ = v___y_6170_;
v___y_6076_ = v___y_6167_;
v___y_6077_ = v___y_6165_;
v___y_6078_ = v___y_6169_;
v___y_6079_ = v_patType_x3f_6163_;
v___y_6080_ = v___y_6168_;
v___y_6081_ = v___y_6158_;
v___y_6082_ = v___x_6171_;
v___y_6083_ = v___y_6161_;
v___y_6084_ = v___y_6164_;
v___y_6085_ = v___y_6159_;
goto v___jp_6068_;
}
else
{
lean_object* v_val_6180_; lean_object* v___x_6182_; uint8_t v_isShared_6183_; uint8_t v_isSharedCheck_6187_; 
v_val_6180_ = lean_ctor_get(v___x_6179_, 0);
v_isSharedCheck_6187_ = !lean_is_exclusive(v___x_6179_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6182_ = v___x_6179_;
v_isShared_6183_ = v_isSharedCheck_6187_;
goto v_resetjp_6181_;
}
else
{
lean_inc(v_val_6180_);
lean_dec(v___x_6179_);
v___x_6182_ = lean_box(0);
v_isShared_6183_ = v_isSharedCheck_6187_;
goto v_resetjp_6181_;
}
v_resetjp_6181_:
{
lean_object* v___x_6185_; 
if (v_isShared_6183_ == 0)
{
v___x_6185_ = v___x_6182_;
goto v_reusejp_6184_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_val_6180_);
v___x_6185_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6184_;
}
v_reusejp_6184_:
{
v___y_6069_ = v___y_6153_;
v___y_6070_ = v___y_6154_;
v___y_6071_ = v___y_6155_;
v___y_6072_ = v___y_6156_;
v___y_6073_ = v___y_6166_;
v___y_6074_ = v___x_6177_;
v___y_6075_ = v___y_6170_;
v___y_6076_ = v___y_6167_;
v___y_6077_ = v___y_6165_;
v___y_6078_ = v___y_6169_;
v___y_6079_ = v_patType_x3f_6163_;
v___y_6080_ = v___y_6168_;
v___y_6081_ = v___y_6158_;
v___y_6082_ = v___x_6171_;
v___y_6083_ = v___y_6161_;
v___y_6084_ = v___y_6164_;
v___y_6085_ = v___x_6185_;
goto v___jp_6068_;
}
}
}
}
}
else
{
lean_dec(v___x_6173_);
lean_inc_n(v___y_6159_, 2);
v___y_6034_ = v___y_6167_;
v___y_6035_ = v___y_6168_;
v___y_6036_ = v___y_6164_;
v___y_6037_ = v___y_6153_;
v___y_6038_ = v___y_6170_;
v___y_6039_ = v___y_6154_;
v___y_6040_ = v___y_6161_;
v___y_6041_ = v___y_6159_;
v___y_6042_ = v___y_6158_;
v___y_6043_ = v___y_6165_;
v___y_6044_ = v___y_6155_;
v___y_6045_ = v___x_6171_;
v___y_6046_ = v___y_6169_;
v___y_6047_ = v_patType_x3f_6163_;
v___y_6048_ = v___y_6156_;
v___y_6049_ = v___y_6166_;
v___y_6050_ = v___y_6159_;
goto v___jp_6033_;
}
}
v___jp_6188_:
{
lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___x_6202_ = l_Lean_Syntax_getArg(v___y_6189_, v___y_6193_);
lean_dec(v___y_6189_);
v___x_6203_ = lean_mk_empty_array_with_capacity(v___x_6088_);
lean_inc(v___y_6192_);
v___x_6204_ = lean_array_push(v___x_6203_, v___y_6192_);
v___x_6205_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6204_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
lean_dec_ref(v___x_6204_);
if (lean_obj_tag(v___x_6205_) == 0)
{
lean_object* v___x_6206_; 
lean_dec_ref_known(v___x_6205_, 1);
v___x_6206_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5963_, v_tk_6087_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
lean_dec(v_tk_6087_);
if (lean_obj_tag(v___x_6206_) == 0)
{
lean_object* v_a_6207_; uint8_t v_kind_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
v_a_6207_ = lean_ctor_get(v___x_6206_, 0);
lean_inc(v_a_6207_);
lean_dec_ref_known(v___x_6206_, 1);
v_kind_6208_ = lean_ctor_get_uint8(v_a_6207_, sizeof(void*)*3);
v___x_6209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_6209_, 0, v_a_6207_);
v___x_6210_ = lean_box(v___y_6190_);
lean_inc(v___y_6192_);
v___x_6211_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_declareMutVar_x3f___boxed), 13, 5);
lean_closure_set(v___x_6211_, 0, lean_box(0));
lean_closure_set(v___x_6211_, 1, v___y_6191_);
lean_closure_set(v___x_6211_, 2, v___y_6192_);
lean_closure_set(v___x_6211_, 3, v___x_6210_);
lean_closure_set(v___x_6211_, 4, v___x_6209_);
v___x_6212_ = l_Lean_Elab_Do_elabDoIdDecl(v___y_6192_, v_xType_x3f_6194_, v___x_6202_, v___x_6211_, v_kind_6208_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
return v___x_6212_;
}
else
{
lean_object* v_a_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6220_; 
lean_dec(v___x_6202_);
lean_dec(v_xType_x3f_6194_);
lean_dec(v___y_6192_);
lean_dec(v___y_6191_);
v_a_6213_ = lean_ctor_get(v___x_6206_, 0);
v_isSharedCheck_6220_ = !lean_is_exclusive(v___x_6206_);
if (v_isSharedCheck_6220_ == 0)
{
v___x_6215_ = v___x_6206_;
v_isShared_6216_ = v_isSharedCheck_6220_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_a_6213_);
lean_dec(v___x_6206_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6220_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v___x_6218_; 
if (v_isShared_6216_ == 0)
{
v___x_6218_ = v___x_6215_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6219_; 
v_reuseFailAlloc_6219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6219_, 0, v_a_6213_);
v___x_6218_ = v_reuseFailAlloc_6219_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
return v___x_6218_;
}
}
}
}
else
{
lean_object* v_a_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6228_; 
lean_dec(v___x_6202_);
lean_dec(v_xType_x3f_6194_);
lean_dec(v___y_6192_);
lean_dec(v___y_6191_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v_a_6221_ = lean_ctor_get(v___x_6205_, 0);
v_isSharedCheck_6228_ = !lean_is_exclusive(v___x_6205_);
if (v_isSharedCheck_6228_ == 0)
{
v___x_6223_ = v___x_6205_;
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_a_6221_);
lean_dec(v___x_6205_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6226_; 
if (v_isShared_6224_ == 0)
{
v___x_6226_ = v___x_6223_;
goto v_reusejp_6225_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
v___x_6226_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6225_;
}
v_reusejp_6225_:
{
return v___x_6226_;
}
}
}
}
v___jp_6229_:
{
uint8_t v___x_6247_; 
lean_inc(v___y_6232_);
v___x_6247_ = l_Lean_Syntax_isOfKind(v___y_6232_, v___y_6238_);
if (v___x_6247_ == 0)
{
uint8_t v___x_6248_; 
lean_dec(v___y_6234_);
lean_inc(v___y_6232_);
v___x_6248_ = l_Lean_Syntax_isOfKind(v___y_6232_, v___y_6237_);
if (v___x_6248_ == 0)
{
lean_object* v___x_6249_; 
lean_dec(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6249_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6249_;
}
else
{
lean_object* v___x_6250_; lean_object* v___x_6251_; uint8_t v___x_6252_; 
v___x_6250_ = l_Lean_Syntax_getArg(v___y_6232_, v___x_5978_);
v___x_6251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetElse___closed__7));
lean_inc(v___x_6250_);
v___x_6252_ = l_Lean_Syntax_isOfKind(v___x_6250_, v___x_6251_);
if (v___x_6252_ == 0)
{
lean_object* v___x_6253_; uint8_t v___x_6254_; 
lean_dec(v_tk_6087_);
v___x_6253_ = l_Lean_Syntax_getArg(v___y_6232_, v___x_6088_);
v___x_6254_ = l_Lean_Syntax_isNone(v___x_6253_);
if (v___x_6254_ == 0)
{
uint8_t v___x_6255_; 
lean_inc(v___x_6253_);
v___x_6255_ = l_Lean_Syntax_matchesNull(v___x_6253_, v___x_6088_);
if (v___x_6255_ == 0)
{
lean_object* v___x_6256_; 
lean_dec(v___x_6253_);
lean_dec(v___x_6250_);
lean_dec(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec_ref(v_dec_5963_);
v___x_6256_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6256_;
}
else
{
lean_object* v___x_6257_; lean_object* v___x_6258_; uint8_t v___x_6259_; 
v___x_6257_ = l_Lean_Syntax_getArg(v___x_6253_, v___x_5978_);
lean_dec(v___x_6253_);
v___x_6258_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6257_);
v___x_6259_ = l_Lean_Syntax_isOfKind(v___x_6257_, v___x_6258_);
if (v___x_6259_ == 0)
{
lean_object* v___x_6260_; 
lean_dec(v___x_6257_);
lean_dec(v___x_6250_);
lean_dec(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec_ref(v_dec_5963_);
v___x_6260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6260_;
}
else
{
lean_object* v___x_6261_; lean_object* v___x_6262_; 
v___x_6261_ = l_Lean_Syntax_getArg(v___x_6257_, v___x_6088_);
lean_dec(v___x_6257_);
v___x_6262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6262_, 0, v___x_6261_);
lean_inc(v___x_6250_);
v___y_6153_ = v___y_6230_;
v___y_6154_ = v___y_6231_;
v___y_6155_ = v___x_6252_;
v___y_6156_ = v___x_6250_;
v___y_6157_ = v___y_6232_;
v___y_6158_ = v___y_6233_;
v___y_6159_ = v___y_6235_;
v___y_6160_ = v___y_6236_;
v___y_6161_ = v___x_6250_;
v___y_6162_ = v___y_6239_;
v_patType_x3f_6163_ = v___x_6262_;
v___y_6164_ = v___y_6240_;
v___y_6165_ = v___y_6241_;
v___y_6166_ = v___y_6242_;
v___y_6167_ = v___y_6243_;
v___y_6168_ = v___y_6244_;
v___y_6169_ = v___y_6245_;
v___y_6170_ = v___y_6246_;
goto v___jp_6152_;
}
}
}
else
{
lean_dec(v___x_6253_);
lean_inc(v___y_6235_);
lean_inc(v___x_6250_);
v___y_6153_ = v___y_6230_;
v___y_6154_ = v___y_6231_;
v___y_6155_ = v___x_6252_;
v___y_6156_ = v___x_6250_;
v___y_6157_ = v___y_6232_;
v___y_6158_ = v___y_6233_;
v___y_6159_ = v___y_6235_;
v___y_6160_ = v___y_6236_;
v___y_6161_ = v___x_6250_;
v___y_6162_ = v___y_6239_;
v_patType_x3f_6163_ = v___y_6235_;
v___y_6164_ = v___y_6240_;
v___y_6165_ = v___y_6241_;
v___y_6166_ = v___y_6242_;
v___y_6167_ = v___y_6243_;
v___y_6168_ = v___y_6244_;
v___y_6169_ = v___y_6245_;
v___y_6170_ = v___y_6246_;
goto v___jp_6152_;
}
}
else
{
lean_object* v___x_6263_; lean_object* v___x_6264_; uint8_t v___x_6265_; 
v___x_6263_ = l_Lean_Syntax_getArg(v___x_6250_, v___x_5978_);
v___x_6264_ = l_Lean_Syntax_getArg(v___y_6232_, v___x_6088_);
v___x_6265_ = l_Lean_Syntax_isNone(v___x_6264_);
if (v___x_6265_ == 0)
{
uint8_t v___x_6266_; 
lean_inc(v___x_6264_);
v___x_6266_ = l_Lean_Syntax_matchesNull(v___x_6264_, v___x_6088_);
if (v___x_6266_ == 0)
{
lean_object* v___x_6267_; 
lean_dec(v___x_6264_);
lean_dec(v___x_6263_);
lean_dec(v___x_6250_);
lean_dec(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6267_;
}
else
{
lean_object* v___x_6268_; lean_object* v___x_6269_; uint8_t v___x_6270_; 
v___x_6268_ = l_Lean_Syntax_getArg(v___x_6264_, v___x_5978_);
lean_dec(v___x_6264_);
v___x_6269_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6268_);
v___x_6270_ = l_Lean_Syntax_isOfKind(v___x_6268_, v___x_6269_);
if (v___x_6270_ == 0)
{
lean_object* v___x_6271_; 
lean_dec(v___x_6268_);
lean_dec(v___x_6263_);
lean_dec(v___x_6250_);
lean_dec(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6271_;
}
else
{
lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6272_ = l_Lean_Syntax_getArg(v___x_6268_, v___x_6088_);
lean_dec(v___x_6268_);
v___x_6273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6273_, 0, v___x_6272_);
lean_inc(v___x_6250_);
v___y_6090_ = v___x_6247_;
v___y_6091_ = v___y_6230_;
v___y_6092_ = v___y_6231_;
v___y_6093_ = v___x_6250_;
v___y_6094_ = v___y_6232_;
v___y_6095_ = v___y_6233_;
v___y_6096_ = v___y_6235_;
v___y_6097_ = v___y_6236_;
v___y_6098_ = v___x_6250_;
v___y_6099_ = v___x_6263_;
v___y_6100_ = v___y_6239_;
v_patType_x3f_6101_ = v___x_6273_;
v___y_6102_ = v___y_6240_;
v___y_6103_ = v___y_6241_;
v___y_6104_ = v___y_6242_;
v___y_6105_ = v___y_6243_;
v___y_6106_ = v___y_6244_;
v___y_6107_ = v___y_6245_;
v___y_6108_ = v___y_6246_;
goto v___jp_6089_;
}
}
}
else
{
lean_dec(v___x_6264_);
lean_inc(v___y_6235_);
lean_inc(v___x_6250_);
v___y_6090_ = v___x_6247_;
v___y_6091_ = v___y_6230_;
v___y_6092_ = v___y_6231_;
v___y_6093_ = v___x_6250_;
v___y_6094_ = v___y_6232_;
v___y_6095_ = v___y_6233_;
v___y_6096_ = v___y_6235_;
v___y_6097_ = v___y_6236_;
v___y_6098_ = v___x_6250_;
v___y_6099_ = v___x_6263_;
v___y_6100_ = v___y_6239_;
v_patType_x3f_6101_ = v___y_6235_;
v___y_6102_ = v___y_6240_;
v___y_6103_ = v___y_6241_;
v___y_6104_ = v___y_6242_;
v___y_6105_ = v___y_6243_;
v___y_6106_ = v___y_6244_;
v___y_6107_ = v___y_6245_;
v___y_6108_ = v___y_6246_;
goto v___jp_6089_;
}
}
}
}
else
{
lean_object* v___x_6274_; lean_object* v___x_6275_; uint8_t v___x_6276_; 
lean_dec(v___y_6231_);
v___x_6274_ = l_Lean_Syntax_getArg(v___y_6232_, v___x_5978_);
v___x_6275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v___x_6274_);
v___x_6276_ = l_Lean_Syntax_isOfKind(v___x_6274_, v___x_6275_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; 
lean_dec(v___x_6274_);
lean_dec(v___y_6234_);
lean_dec(v___y_6232_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6277_;
}
else
{
lean_object* v___x_6278_; uint8_t v___x_6279_; 
v___x_6278_ = l_Lean_Syntax_getArg(v___y_6232_, v___x_6088_);
v___x_6279_ = l_Lean_Syntax_isNone(v___x_6278_);
if (v___x_6279_ == 0)
{
uint8_t v___x_6280_; 
lean_inc(v___x_6278_);
v___x_6280_ = l_Lean_Syntax_matchesNull(v___x_6278_, v___x_6088_);
if (v___x_6280_ == 0)
{
lean_object* v___x_6281_; 
lean_dec(v___x_6278_);
lean_dec(v___x_6274_);
lean_dec(v___y_6234_);
lean_dec(v___y_6232_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6281_;
}
else
{
lean_object* v___x_6282_; lean_object* v___x_6283_; uint8_t v___x_6284_; 
v___x_6282_ = l_Lean_Syntax_getArg(v___x_6278_, v___x_5978_);
lean_dec(v___x_6278_);
v___x_6283_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6282_);
v___x_6284_ = l_Lean_Syntax_isOfKind(v___x_6282_, v___x_6283_);
if (v___x_6284_ == 0)
{
lean_object* v___x_6285_; 
lean_dec(v___x_6282_);
lean_dec(v___x_6274_);
lean_dec(v___y_6234_);
lean_dec(v___y_6232_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___x_6285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6285_;
}
else
{
lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6286_ = l_Lean_Syntax_getArg(v___x_6282_, v___x_6088_);
lean_dec(v___x_6282_);
v___x_6287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6287_, 0, v___x_6286_);
v___y_6189_ = v___y_6232_;
v___y_6190_ = v___y_6233_;
v___y_6191_ = v___y_6234_;
v___y_6192_ = v___x_6274_;
v___y_6193_ = v___y_6239_;
v_xType_x3f_6194_ = v___x_6287_;
v___y_6195_ = v___y_6240_;
v___y_6196_ = v___y_6241_;
v___y_6197_ = v___y_6242_;
v___y_6198_ = v___y_6243_;
v___y_6199_ = v___y_6244_;
v___y_6200_ = v___y_6245_;
v___y_6201_ = v___y_6246_;
goto v___jp_6188_;
}
}
}
else
{
lean_dec(v___x_6278_);
lean_inc(v___y_6235_);
v___y_6189_ = v___y_6232_;
v___y_6190_ = v___y_6233_;
v___y_6191_ = v___y_6234_;
v___y_6192_ = v___x_6274_;
v___y_6193_ = v___y_6239_;
v_xType_x3f_6194_ = v___y_6235_;
v___y_6195_ = v___y_6240_;
v___y_6196_ = v___y_6241_;
v___y_6197_ = v___y_6242_;
v___y_6198_ = v___y_6243_;
v___y_6199_ = v___y_6244_;
v___y_6200_ = v___y_6245_;
v___y_6201_ = v___y_6246_;
goto v___jp_6188_;
}
}
}
}
v___jp_6288_:
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v_a_6309_; lean_object* v___x_6311_; uint8_t v_isShared_6312_; uint8_t v_isSharedCheck_6316_; 
lean_dec(v___y_6294_);
lean_dec(v___y_6292_);
lean_dec(v___y_6290_);
v___x_6307_ = lean_obj_once(&l_Lean_Elab_Do_elabDoLetArrow___closed__1, &l_Lean_Elab_Do_elabDoLetArrow___closed__1_once, _init_l_Lean_Elab_Do_elabDoLetArrow___closed__1);
v___x_6308_ = l_Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0___redArg(v___y_6299_, v___x_6307_, v___y_6305_, v___y_6298_, v___y_6302_, v___y_6296_, v___y_6297_, v___y_6291_, v___y_6293_);
lean_dec(v___y_6299_);
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6316_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6316_ == 0)
{
v___x_6311_ = v___x_6308_;
v_isShared_6312_ = v_isSharedCheck_6316_;
goto v_resetjp_6310_;
}
else
{
lean_inc(v_a_6309_);
lean_dec(v___x_6308_);
v___x_6311_ = lean_box(0);
v_isShared_6312_ = v_isSharedCheck_6316_;
goto v_resetjp_6310_;
}
v_resetjp_6310_:
{
lean_object* v___x_6314_; 
if (v_isShared_6312_ == 0)
{
v___x_6314_ = v___x_6311_;
goto v_reusejp_6313_;
}
else
{
lean_object* v_reuseFailAlloc_6315_; 
v_reuseFailAlloc_6315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6315_, 0, v_a_6309_);
v___x_6314_ = v_reuseFailAlloc_6315_;
goto v_reusejp_6313_;
}
v_reusejp_6313_:
{
return v___x_6314_;
}
}
}
v___jp_6317_:
{
if (v___y_6337_ == 0)
{
lean_object* v_eq_x3f_6338_; 
v_eq_x3f_6338_ = lean_ctor_get(v___y_6331_, 0);
lean_inc(v_eq_x3f_6338_);
lean_dec_ref(v___y_6331_);
if (lean_obj_tag(v_eq_x3f_6338_) == 0)
{
lean_dec(v___y_6328_);
v___y_6230_ = v___y_6318_;
v___y_6231_ = v___y_6319_;
v___y_6232_ = v___y_6321_;
v___y_6233_ = v___y_6330_;
v___y_6234_ = v___y_6323_;
v___y_6235_ = v___y_6333_;
v___y_6236_ = v___y_6334_;
v___y_6237_ = v___y_6324_;
v___y_6238_ = v___y_6329_;
v___y_6239_ = v___y_6336_;
v___y_6240_ = v___y_6335_;
v___y_6241_ = v___y_6327_;
v___y_6242_ = v___y_6332_;
v___y_6243_ = v___y_6325_;
v___y_6244_ = v___y_6326_;
v___y_6245_ = v___y_6320_;
v___y_6246_ = v___y_6322_;
goto v___jp_6229_;
}
else
{
lean_dec_ref_known(v_eq_x3f_6338_, 1);
if (v___x_5976_ == 0)
{
lean_dec(v___y_6328_);
v___y_6230_ = v___y_6318_;
v___y_6231_ = v___y_6319_;
v___y_6232_ = v___y_6321_;
v___y_6233_ = v___y_6330_;
v___y_6234_ = v___y_6323_;
v___y_6235_ = v___y_6333_;
v___y_6236_ = v___y_6334_;
v___y_6237_ = v___y_6324_;
v___y_6238_ = v___y_6329_;
v___y_6239_ = v___y_6336_;
v___y_6240_ = v___y_6335_;
v___y_6241_ = v___y_6327_;
v___y_6242_ = v___y_6332_;
v___y_6243_ = v___y_6325_;
v___y_6244_ = v___y_6326_;
v___y_6245_ = v___y_6320_;
v___y_6246_ = v___y_6322_;
goto v___jp_6229_;
}
else
{
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___y_6289_ = v___y_6318_;
v___y_6290_ = v___y_6319_;
v___y_6291_ = v___y_6320_;
v___y_6292_ = v___y_6321_;
v___y_6293_ = v___y_6322_;
v___y_6294_ = v___y_6323_;
v___y_6295_ = v___y_6324_;
v___y_6296_ = v___y_6325_;
v___y_6297_ = v___y_6326_;
v___y_6298_ = v___y_6327_;
v___y_6299_ = v___y_6328_;
v___y_6300_ = v___y_6329_;
v___y_6301_ = v___y_6330_;
v___y_6302_ = v___y_6332_;
v___y_6303_ = v___y_6333_;
v___y_6304_ = v___y_6334_;
v___y_6305_ = v___y_6335_;
v___y_6306_ = v___y_6336_;
goto v___jp_6288_;
}
}
}
else
{
lean_dec_ref(v___y_6331_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v___y_6289_ = v___y_6318_;
v___y_6290_ = v___y_6319_;
v___y_6291_ = v___y_6320_;
v___y_6292_ = v___y_6321_;
v___y_6293_ = v___y_6322_;
v___y_6294_ = v___y_6323_;
v___y_6295_ = v___y_6324_;
v___y_6296_ = v___y_6325_;
v___y_6297_ = v___y_6326_;
v___y_6298_ = v___y_6327_;
v___y_6299_ = v___y_6328_;
v___y_6300_ = v___y_6329_;
v___y_6301_ = v___y_6330_;
v___y_6302_ = v___y_6332_;
v___y_6303_ = v___y_6333_;
v___y_6304_ = v___y_6334_;
v___y_6305_ = v___y_6335_;
v___y_6306_ = v___y_6336_;
goto v___jp_6288_;
}
}
v___jp_6339_:
{
if (v___y_6359_ == 0)
{
uint8_t v_zeta_6360_; 
v_zeta_6360_ = lean_ctor_get_uint8(v___y_6355_, sizeof(void*)*1 + 2);
v___y_6318_ = v___y_6340_;
v___y_6319_ = v___y_6341_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6343_;
v___y_6322_ = v___y_6344_;
v___y_6323_ = v___y_6345_;
v___y_6324_ = v___y_6346_;
v___y_6325_ = v___y_6347_;
v___y_6326_ = v___y_6348_;
v___y_6327_ = v___y_6349_;
v___y_6328_ = v___y_6350_;
v___y_6329_ = v___y_6351_;
v___y_6330_ = v___y_6352_;
v___y_6331_ = v___y_6355_;
v___y_6332_ = v___y_6354_;
v___y_6333_ = v___y_6353_;
v___y_6334_ = v___y_6356_;
v___y_6335_ = v___y_6357_;
v___y_6336_ = v___y_6358_;
v___y_6337_ = v_zeta_6360_;
goto v___jp_6317_;
}
else
{
v___y_6318_ = v___y_6340_;
v___y_6319_ = v___y_6341_;
v___y_6320_ = v___y_6342_;
v___y_6321_ = v___y_6343_;
v___y_6322_ = v___y_6344_;
v___y_6323_ = v___y_6345_;
v___y_6324_ = v___y_6346_;
v___y_6325_ = v___y_6347_;
v___y_6326_ = v___y_6348_;
v___y_6327_ = v___y_6349_;
v___y_6328_ = v___y_6350_;
v___y_6329_ = v___y_6351_;
v___y_6330_ = v___y_6352_;
v___y_6331_ = v___y_6355_;
v___y_6332_ = v___y_6354_;
v___y_6333_ = v___y_6353_;
v___y_6334_ = v___y_6356_;
v___y_6335_ = v___y_6357_;
v___y_6336_ = v___y_6358_;
v___y_6337_ = v___x_5976_;
goto v___jp_6317_;
}
}
v___jp_6361_:
{
lean_object* v___x_6370_; lean_object* v_cfg_6371_; lean_object* v___x_6372_; uint8_t v___x_6373_; 
v___x_6370_ = lean_unsigned_to_nat(2u);
v_cfg_6371_ = l_Lean_Syntax_getArg(v_stx_5962_, v___x_6370_);
v___x_6372_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__3));
lean_inc(v_cfg_6371_);
v___x_6373_ = l_Lean_Syntax_isOfKind(v_cfg_6371_, v___x_6372_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6374_; 
lean_dec(v_cfg_6371_);
lean_dec(v_mutTk_x3f_6362_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
lean_dec(v_stx_5962_);
v___x_6374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6374_;
}
else
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; uint8_t v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6375_ = lean_unsigned_to_nat(3u);
v___x_6376_ = l_Lean_Syntax_getArg(v_stx_5962_, v___x_6375_);
lean_dec(v_stx_5962_);
v___x_6377_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
v___x_6378_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
v___x_6379_ = 0;
v___x_6380_ = lean_box(0);
v___x_6381_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLet___closed__4));
lean_inc(v_cfg_6371_);
v___x_6382_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_getLetConfigAndCheckMut(v_cfg_6371_, v_mutTk_x3f_6362_, v___x_6381_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_);
if (lean_obj_tag(v___x_6382_) == 0)
{
lean_object* v_a_6383_; lean_object* v___x_6384_; 
v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
lean_inc(v_a_6383_);
lean_dec_ref_known(v___x_6382_, 1);
v___x_6384_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_checkLetConfigInDo___redArg(v_a_6383_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_);
if (lean_obj_tag(v___x_6384_) == 0)
{
uint8_t v_nondep_6385_; 
lean_dec_ref_known(v___x_6384_, 1);
v_nondep_6385_ = lean_ctor_get_uint8(v_a_6383_, sizeof(void*)*1);
if (v_nondep_6385_ == 0)
{
uint8_t v_usedOnly_6386_; 
v_usedOnly_6386_ = lean_ctor_get_uint8(v_a_6383_, sizeof(void*)*1 + 1);
lean_inc(v_mutTk_x3f_6362_);
v___y_6340_ = v___x_6372_;
v___y_6341_ = v_mutTk_x3f_6362_;
v___y_6342_ = v___y_6368_;
v___y_6343_ = v___x_6376_;
v___y_6344_ = v___y_6369_;
v___y_6345_ = v_mutTk_x3f_6362_;
v___y_6346_ = v___x_6378_;
v___y_6347_ = v___y_6366_;
v___y_6348_ = v___y_6367_;
v___y_6349_ = v___y_6364_;
v___y_6350_ = v_cfg_6371_;
v___y_6351_ = v___x_6377_;
v___y_6352_ = v___x_6379_;
v___y_6353_ = v___x_6380_;
v___y_6354_ = v___y_6365_;
v___y_6355_ = v_a_6383_;
v___y_6356_ = v___x_6370_;
v___y_6357_ = v___y_6363_;
v___y_6358_ = v___x_6375_;
v___y_6359_ = v_usedOnly_6386_;
goto v___jp_6339_;
}
else
{
lean_inc(v_mutTk_x3f_6362_);
v___y_6340_ = v___x_6372_;
v___y_6341_ = v_mutTk_x3f_6362_;
v___y_6342_ = v___y_6368_;
v___y_6343_ = v___x_6376_;
v___y_6344_ = v___y_6369_;
v___y_6345_ = v_mutTk_x3f_6362_;
v___y_6346_ = v___x_6378_;
v___y_6347_ = v___y_6366_;
v___y_6348_ = v___y_6367_;
v___y_6349_ = v___y_6364_;
v___y_6350_ = v_cfg_6371_;
v___y_6351_ = v___x_6377_;
v___y_6352_ = v___x_6379_;
v___y_6353_ = v___x_6380_;
v___y_6354_ = v___y_6365_;
v___y_6355_ = v_a_6383_;
v___y_6356_ = v___x_6370_;
v___y_6357_ = v___y_6363_;
v___y_6358_ = v___x_6375_;
v___y_6359_ = v___x_5976_;
goto v___jp_6339_;
}
}
else
{
lean_object* v_a_6387_; lean_object* v___x_6389_; uint8_t v_isShared_6390_; uint8_t v_isSharedCheck_6394_; 
lean_dec(v_a_6383_);
lean_dec(v___x_6376_);
lean_dec(v_cfg_6371_);
lean_dec(v_mutTk_x3f_6362_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v_a_6387_ = lean_ctor_get(v___x_6384_, 0);
v_isSharedCheck_6394_ = !lean_is_exclusive(v___x_6384_);
if (v_isSharedCheck_6394_ == 0)
{
v___x_6389_ = v___x_6384_;
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
else
{
lean_inc(v_a_6387_);
lean_dec(v___x_6384_);
v___x_6389_ = lean_box(0);
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
v_resetjp_6388_:
{
lean_object* v___x_6392_; 
if (v_isShared_6390_ == 0)
{
v___x_6392_ = v___x_6389_;
goto v_reusejp_6391_;
}
else
{
lean_object* v_reuseFailAlloc_6393_; 
v_reuseFailAlloc_6393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_a_6387_);
v___x_6392_ = v_reuseFailAlloc_6393_;
goto v_reusejp_6391_;
}
v_reusejp_6391_:
{
return v___x_6392_;
}
}
}
}
else
{
lean_object* v_a_6395_; lean_object* v___x_6397_; uint8_t v_isShared_6398_; uint8_t v_isSharedCheck_6402_; 
lean_dec(v___x_6376_);
lean_dec(v_cfg_6371_);
lean_dec(v_mutTk_x3f_6362_);
lean_dec(v_tk_6087_);
lean_dec_ref(v_dec_5963_);
v_a_6395_ = lean_ctor_get(v___x_6382_, 0);
v_isSharedCheck_6402_ = !lean_is_exclusive(v___x_6382_);
if (v_isSharedCheck_6402_ == 0)
{
v___x_6397_ = v___x_6382_;
v_isShared_6398_ = v_isSharedCheck_6402_;
goto v_resetjp_6396_;
}
else
{
lean_inc(v_a_6395_);
lean_dec(v___x_6382_);
v___x_6397_ = lean_box(0);
v_isShared_6398_ = v_isSharedCheck_6402_;
goto v_resetjp_6396_;
}
v_resetjp_6396_:
{
lean_object* v___x_6400_; 
if (v_isShared_6398_ == 0)
{
v___x_6400_ = v___x_6397_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6395_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
return v___x_6400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoLetArrow___boxed(lean_object* v_stx_6410_, lean_object* v_dec_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_, lean_object* v_a_6414_, lean_object* v_a_6415_, lean_object* v_a_6416_, lean_object* v_a_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_){
_start:
{
lean_object* v_res_6420_; 
v_res_6420_ = l_Lean_Elab_Do_elabDoLetArrow(v_stx_6410_, v_dec_6411_, v_a_6412_, v_a_6413_, v_a_6414_, v_a_6415_, v_a_6416_, v_a_6417_, v_a_6418_);
lean_dec(v_a_6418_);
lean_dec_ref(v_a_6417_);
lean_dec(v_a_6416_);
lean_dec_ref(v_a_6415_);
lean_dec(v_a_6414_);
lean_dec_ref(v_a_6413_);
lean_dec_ref(v_a_6412_);
return v_res_6420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1(){
_start:
{
lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; 
v___x_6428_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6429_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__15));
v___x_6430_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___closed__1));
v___x_6431_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoLetArrow___boxed), 10, 0);
v___x_6432_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6428_, v___x_6429_, v___x_6430_, v___x_6431_);
return v___x_6432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1___boxed(lean_object* v_a_6433_){
_start:
{
lean_object* v_res_6434_; 
v_res_6434_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoLetArrow___regBuiltin_Lean_Elab_Do_elabDoLetArrow__1();
return v_res_6434_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3(void){
_start:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6442_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__2));
v___x_6443_ = l_Lean_stringToMessageData(v___x_6442_);
return v___x_6443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow(lean_object* v_stx_6444_, lean_object* v_dec_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_, lean_object* v_a_6452_){
_start:
{
lean_object* v___x_6454_; uint8_t v___x_6455_; 
v___x_6454_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
lean_inc(v_stx_6444_);
v___x_6455_ = l_Lean_Syntax_isOfKind(v_stx_6444_, v___x_6454_);
if (v___x_6455_ == 0)
{
lean_object* v___x_6456_; 
lean_dec_ref(v_dec_6445_);
lean_dec(v_stx_6444_);
v___x_6456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6456_;
}
else
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; uint8_t v___x_6460_; 
v___x_6457_ = lean_unsigned_to_nat(0u);
v___x_6458_ = l_Lean_Syntax_getArg(v_stx_6444_, v___x_6457_);
lean_dec(v_stx_6444_);
v___x_6459_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__17));
lean_inc(v___x_6458_);
v___x_6460_ = l_Lean_Syntax_isOfKind(v___x_6458_, v___x_6459_);
if (v___x_6460_ == 0)
{
lean_object* v___x_6461_; uint8_t v___x_6462_; 
v___x_6461_ = ((lean_object*)(l_Lean_Elab_Do_elabDoLetArrow___closed__3));
lean_inc(v___x_6458_);
v___x_6462_ = l_Lean_Syntax_isOfKind(v___x_6458_, v___x_6461_);
if (v___x_6462_ == 0)
{
lean_object* v___x_6463_; 
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6463_;
}
else
{
lean_object* v___x_6464_; lean_object* v___y_6466_; lean_object* v___y_6467_; lean_object* v___y_6468_; lean_object* v___y_6469_; lean_object* v___y_6470_; lean_object* v___y_6471_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; lean_object* v___y_6503_; lean_object* v___y_6504_; lean_object* v___y_6505_; lean_object* v___y_6506_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; uint8_t v___y_6512_; lean_object* v___y_6524_; lean_object* v___y_6525_; lean_object* v___y_6526_; lean_object* v___y_6527_; lean_object* v___y_6528_; lean_object* v___y_6529_; lean_object* v___y_6530_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; uint8_t v___y_6534_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___x_6549_; lean_object* v_t_x3f_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___x_6580_; uint8_t v___x_6581_; 
v___x_6464_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6457_);
v___x_6549_ = lean_unsigned_to_nat(1u);
v___x_6580_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6549_);
v___x_6581_ = l_Lean_Syntax_isNone(v___x_6580_);
if (v___x_6581_ == 0)
{
uint8_t v___x_6582_; 
lean_inc(v___x_6580_);
v___x_6582_ = l_Lean_Syntax_matchesNull(v___x_6580_, v___x_6549_);
if (v___x_6582_ == 0)
{
lean_object* v___x_6583_; 
lean_dec(v___x_6580_);
lean_dec(v___x_6464_);
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6583_;
}
else
{
lean_object* v___x_6584_; lean_object* v___x_6585_; uint8_t v___x_6586_; 
v___x_6584_ = l_Lean_Syntax_getArg(v___x_6580_, v___x_6457_);
lean_dec(v___x_6580_);
v___x_6585_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6584_);
v___x_6586_ = l_Lean_Syntax_isOfKind(v___x_6584_, v___x_6585_);
if (v___x_6586_ == 0)
{
lean_object* v___x_6587_; 
lean_dec(v___x_6584_);
lean_dec(v___x_6464_);
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6587_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6587_;
}
else
{
lean_object* v_t_x3f_6588_; lean_object* v___x_6589_; 
v_t_x3f_6588_ = l_Lean_Syntax_getArg(v___x_6584_, v___x_6549_);
lean_dec(v___x_6584_);
v___x_6589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6589_, 0, v_t_x3f_6588_);
v_t_x3f_6551_ = v___x_6589_;
v___y_6552_ = v_a_6446_;
v___y_6553_ = v_a_6447_;
v___y_6554_ = v_a_6448_;
v___y_6555_ = v_a_6449_;
v___y_6556_ = v_a_6450_;
v___y_6557_ = v_a_6451_;
v___y_6558_ = v_a_6452_;
goto v___jp_6550_;
}
}
}
else
{
lean_object* v___x_6590_; 
lean_dec(v___x_6580_);
v___x_6590_ = lean_box(0);
v_t_x3f_6551_ = v___x_6590_;
v___y_6552_ = v_a_6446_;
v___y_6553_ = v_a_6447_;
v___y_6554_ = v_a_6448_;
v___y_6555_ = v_a_6449_;
v___y_6556_ = v_a_6450_;
v___y_6557_ = v_a_6451_;
v___y_6558_ = v_a_6452_;
goto v___jp_6550_;
}
v___jp_6465_:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6475_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6476_ = l_Lean_Core_mkFreshUserName(v___x_6475_, v___y_6473_, v___y_6474_);
if (lean_obj_tag(v___x_6476_) == 0)
{
lean_object* v_a_6477_; lean_object* v_ref_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; uint8_t v_kind_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v_a_6477_ = lean_ctor_get(v___x_6476_, 0);
lean_inc(v_a_6477_);
lean_dec_ref_known(v___x_6476_, 1);
v_ref_6478_ = lean_ctor_get(v___y_6473_, 2);
v___x_6479_ = l_Lean_mkIdentFrom(v___x_6464_, v_a_6477_, v___x_6460_);
v___x_6480_ = l_Lean_SourceInfo_fromRef(v_ref_6478_, v___x_6460_);
v___x_6481_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6482_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__10));
v___x_6483_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6484_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
lean_inc_n(v___x_6480_, 3);
v___x_6485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6485_, 0, v___x_6480_);
lean_ctor_set(v___x_6485_, 1, v___x_6483_);
lean_ctor_set(v___x_6485_, 2, v___x_6484_);
v___x_6486_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6487_, 0, v___x_6480_);
lean_ctor_set(v___x_6487_, 1, v___x_6486_);
lean_inc(v___x_6479_);
lean_inc_ref(v___x_6485_);
v___x_6488_ = l_Lean_Syntax_node5(v___x_6480_, v___x_6482_, v___x_6464_, v___x_6485_, v___x_6485_, v___x_6487_, v___x_6479_);
v_kind_6489_ = lean_ctor_get_uint8(v_dec_6445_, sizeof(void*)*3);
v___x_6490_ = l_Lean_Syntax_node1(v___x_6480_, v___x_6481_, v___x_6488_);
v___x_6491_ = lean_box(v___x_6455_);
v___x_6492_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6492_, 0, v___x_6490_);
lean_closure_set(v___x_6492_, 1, v_dec_6445_);
lean_closure_set(v___x_6492_, 2, v___x_6491_);
v___x_6493_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6479_, v___y_6467_, v___y_6466_, v___x_6492_, v_kind_6489_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_);
return v___x_6493_;
}
else
{
lean_object* v_a_6494_; lean_object* v___x_6496_; uint8_t v_isShared_6497_; uint8_t v_isSharedCheck_6501_; 
lean_dec(v___y_6467_);
lean_dec(v___y_6466_);
lean_dec(v___x_6464_);
lean_dec_ref(v_dec_6445_);
v_a_6494_ = lean_ctor_get(v___x_6476_, 0);
v_isSharedCheck_6501_ = !lean_is_exclusive(v___x_6476_);
if (v_isSharedCheck_6501_ == 0)
{
v___x_6496_ = v___x_6476_;
v_isShared_6497_ = v_isSharedCheck_6501_;
goto v_resetjp_6495_;
}
else
{
lean_inc(v_a_6494_);
lean_dec(v___x_6476_);
v___x_6496_ = lean_box(0);
v_isShared_6497_ = v_isSharedCheck_6501_;
goto v_resetjp_6495_;
}
v_resetjp_6495_:
{
lean_object* v___x_6499_; 
if (v_isShared_6497_ == 0)
{
v___x_6499_ = v___x_6496_;
goto v_reusejp_6498_;
}
else
{
lean_object* v_reuseFailAlloc_6500_; 
v_reuseFailAlloc_6500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_a_6494_);
v___x_6499_ = v_reuseFailAlloc_6500_;
goto v_reusejp_6498_;
}
v_reusejp_6498_:
{
return v___x_6499_;
}
}
}
}
v___jp_6502_:
{
if (v___y_6512_ == 0)
{
lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v_a_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6522_; 
lean_dec(v___y_6510_);
lean_dec(v___y_6509_);
lean_dec(v___x_6464_);
lean_dec_ref(v_dec_6445_);
v___x_6513_ = lean_obj_once(&l_Lean_Elab_Do_elabDoReassignArrow___closed__3, &l_Lean_Elab_Do_elabDoReassignArrow___closed__3_once, _init_l_Lean_Elab_Do_elabDoReassignArrow___closed__3);
v___x_6514_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Do_LetOrReassign_checkMutVars_spec__0_spec__0___redArg(v___x_6513_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6507_);
v_a_6515_ = lean_ctor_get(v___x_6514_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6517_ = v___x_6514_;
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_a_6515_);
lean_dec(v___x_6514_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v___x_6520_; 
if (v_isShared_6518_ == 0)
{
v___x_6520_ = v___x_6517_;
goto v_reusejp_6519_;
}
else
{
lean_object* v_reuseFailAlloc_6521_; 
v_reuseFailAlloc_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
v___x_6520_ = v_reuseFailAlloc_6521_;
goto v_reusejp_6519_;
}
v_reusejp_6519_:
{
return v___x_6520_;
}
}
}
else
{
v___y_6466_ = v___y_6509_;
v___y_6467_ = v___y_6510_;
v___y_6468_ = v___y_6508_;
v___y_6469_ = v___y_6506_;
v___y_6470_ = v___y_6511_;
v___y_6471_ = v___y_6503_;
v___y_6472_ = v___y_6504_;
v___y_6473_ = v___y_6505_;
v___y_6474_ = v___y_6507_;
goto v___jp_6465_;
}
}
v___jp_6523_:
{
if (v___y_6534_ == 0)
{
lean_dec(v___y_6526_);
v___y_6503_ = v___y_6524_;
v___y_6504_ = v___y_6525_;
v___y_6505_ = v___y_6527_;
v___y_6506_ = v___y_6529_;
v___y_6507_ = v___y_6528_;
v___y_6508_ = v___y_6530_;
v___y_6509_ = v___y_6531_;
v___y_6510_ = v___y_6532_;
v___y_6511_ = v___y_6533_;
v___y_6512_ = v___x_6460_;
goto v___jp_6502_;
}
else
{
if (lean_obj_tag(v___y_6526_) == 0)
{
v___y_6503_ = v___y_6524_;
v___y_6504_ = v___y_6525_;
v___y_6505_ = v___y_6527_;
v___y_6506_ = v___y_6529_;
v___y_6507_ = v___y_6528_;
v___y_6508_ = v___y_6530_;
v___y_6509_ = v___y_6531_;
v___y_6510_ = v___y_6532_;
v___y_6511_ = v___y_6533_;
v___y_6512_ = v___x_6462_;
goto v___jp_6502_;
}
else
{
lean_object* v_val_6535_; 
v_val_6535_ = lean_ctor_get(v___y_6526_, 0);
lean_inc(v_val_6535_);
lean_dec_ref_known(v___y_6526_, 1);
if (lean_obj_tag(v_val_6535_) == 0)
{
v___y_6503_ = v___y_6524_;
v___y_6504_ = v___y_6525_;
v___y_6505_ = v___y_6527_;
v___y_6506_ = v___y_6529_;
v___y_6507_ = v___y_6528_;
v___y_6508_ = v___y_6530_;
v___y_6509_ = v___y_6531_;
v___y_6510_ = v___y_6532_;
v___y_6511_ = v___y_6533_;
v___y_6512_ = v___x_6462_;
goto v___jp_6502_;
}
else
{
lean_dec_ref_known(v_val_6535_, 1);
v___y_6503_ = v___y_6524_;
v___y_6504_ = v___y_6525_;
v___y_6505_ = v___y_6527_;
v___y_6506_ = v___y_6529_;
v___y_6507_ = v___y_6528_;
v___y_6508_ = v___y_6530_;
v___y_6509_ = v___y_6531_;
v___y_6510_ = v___y_6532_;
v___y_6511_ = v___y_6533_;
v___y_6512_ = v___x_6460_;
goto v___jp_6502_;
}
}
}
}
v___jp_6536_:
{
lean_object* v___x_6548_; 
lean_dec(v___y_6544_);
v___x_6548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6548_, 0, v___y_6547_);
v___y_6524_ = v___y_6541_;
v___y_6525_ = v___y_6540_;
v___y_6526_ = v___x_6548_;
v___y_6527_ = v___y_6546_;
v___y_6528_ = v___y_6538_;
v___y_6529_ = v___y_6537_;
v___y_6530_ = v___y_6539_;
v___y_6531_ = v___y_6543_;
v___y_6532_ = v___y_6545_;
v___y_6533_ = v___y_6542_;
v___y_6534_ = v___x_6460_;
goto v___jp_6523_;
}
v___jp_6550_:
{
lean_object* v___x_6559_; lean_object* v_rhs_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; uint8_t v___x_6563_; 
v___x_6559_ = lean_unsigned_to_nat(3u);
v_rhs_6560_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6559_);
v___x_6561_ = lean_unsigned_to_nat(4u);
v___x_6562_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6561_);
lean_dec(v___x_6458_);
v___x_6563_ = l_Lean_Syntax_isNone(v___x_6562_);
if (v___x_6563_ == 0)
{
uint8_t v___x_6564_; 
lean_inc(v___x_6562_);
v___x_6564_ = l_Lean_Syntax_matchesNull(v___x_6562_, v___x_6559_);
if (v___x_6564_ == 0)
{
lean_object* v___x_6565_; 
lean_dec(v___x_6562_);
lean_dec(v_rhs_6560_);
lean_dec(v_t_x3f_6551_);
lean_dec(v___x_6464_);
lean_dec_ref(v_dec_6445_);
v___x_6565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6565_;
}
else
{
lean_object* v___x_6566_; lean_object* v_otherwise_x3f_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6566_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_6567_ = l_Lean_Syntax_getArg(v___x_6562_, v___x_6549_);
v___x_6568_ = l_Lean_Syntax_getArg(v___x_6562_, v___x_6566_);
lean_dec(v___x_6562_);
v___x_6569_ = l_Lean_Syntax_getOptional_x3f(v___x_6568_);
lean_dec(v___x_6568_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v___x_6570_; 
v___x_6570_ = lean_box(0);
v___y_6537_ = v___y_6553_;
v___y_6538_ = v___y_6558_;
v___y_6539_ = v___y_6552_;
v___y_6540_ = v___y_6556_;
v___y_6541_ = v___y_6555_;
v___y_6542_ = v___y_6554_;
v___y_6543_ = v_rhs_6560_;
v___y_6544_ = v_otherwise_x3f_6567_;
v___y_6545_ = v_t_x3f_6551_;
v___y_6546_ = v___y_6557_;
v___y_6547_ = v___x_6570_;
goto v___jp_6536_;
}
else
{
lean_object* v_val_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6578_; 
v_val_6571_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6578_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6578_ == 0)
{
v___x_6573_ = v___x_6569_;
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_val_6571_);
lean_dec(v___x_6569_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
lean_object* v___x_6576_; 
if (v_isShared_6574_ == 0)
{
v___x_6576_ = v___x_6573_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v_val_6571_);
v___x_6576_ = v_reuseFailAlloc_6577_;
goto v_reusejp_6575_;
}
v_reusejp_6575_:
{
v___y_6537_ = v___y_6553_;
v___y_6538_ = v___y_6558_;
v___y_6539_ = v___y_6552_;
v___y_6540_ = v___y_6556_;
v___y_6541_ = v___y_6555_;
v___y_6542_ = v___y_6554_;
v___y_6543_ = v_rhs_6560_;
v___y_6544_ = v_otherwise_x3f_6567_;
v___y_6545_ = v_t_x3f_6551_;
v___y_6546_ = v___y_6557_;
v___y_6547_ = v___x_6576_;
goto v___jp_6536_;
}
}
}
}
}
else
{
lean_object* v___x_6579_; 
lean_dec(v___x_6562_);
v___x_6579_ = lean_box(0);
v___y_6524_ = v___y_6555_;
v___y_6525_ = v___y_6556_;
v___y_6526_ = v___x_6579_;
v___y_6527_ = v___y_6557_;
v___y_6528_ = v___y_6558_;
v___y_6529_ = v___y_6553_;
v___y_6530_ = v___y_6552_;
v___y_6531_ = v_rhs_6560_;
v___y_6532_ = v_t_x3f_6551_;
v___y_6533_ = v___y_6554_;
v___y_6534_ = v___x_6462_;
goto v___jp_6523_;
}
}
}
}
else
{
lean_object* v_x_6591_; lean_object* v___y_6593_; lean_object* v_t_6594_; lean_object* v___y_6595_; lean_object* v___y_6596_; lean_object* v___y_6597_; lean_object* v___y_6598_; lean_object* v___y_6599_; lean_object* v___y_6600_; lean_object* v___y_6601_; lean_object* v_t_x3f_6634_; lean_object* v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; lean_object* v___y_6638_; lean_object* v___y_6639_; lean_object* v___y_6640_; lean_object* v___y_6641_; lean_object* v___x_6676_; uint8_t v___x_6677_; 
v_x_6591_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6457_);
v___x_6676_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__43));
lean_inc(v_x_6591_);
v___x_6677_ = l_Lean_Syntax_isOfKind(v_x_6591_, v___x_6676_);
if (v___x_6677_ == 0)
{
lean_object* v___x_6678_; 
lean_dec(v_x_6591_);
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6678_;
}
else
{
lean_object* v___x_6679_; lean_object* v___x_6680_; uint8_t v___x_6681_; 
v___x_6679_ = lean_unsigned_to_nat(1u);
v___x_6680_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6679_);
v___x_6681_ = l_Lean_Syntax_isNone(v___x_6680_);
if (v___x_6681_ == 0)
{
uint8_t v___x_6682_; 
lean_inc(v___x_6680_);
v___x_6682_ = l_Lean_Syntax_matchesNull(v___x_6680_, v___x_6679_);
if (v___x_6682_ == 0)
{
lean_object* v___x_6683_; 
lean_dec(v___x_6680_);
lean_dec(v_x_6591_);
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6683_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6683_;
}
else
{
lean_object* v___x_6684_; lean_object* v___x_6685_; uint8_t v___x_6686_; 
v___x_6684_ = l_Lean_Syntax_getArg(v___x_6680_, v___x_6457_);
lean_dec(v___x_6680_);
v___x_6685_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__39));
lean_inc(v___x_6684_);
v___x_6686_ = l_Lean_Syntax_isOfKind(v___x_6684_, v___x_6685_);
if (v___x_6686_ == 0)
{
lean_object* v___x_6687_; 
lean_dec(v___x_6684_);
lean_dec(v_x_6591_);
lean_dec(v___x_6458_);
lean_dec_ref(v_dec_6445_);
v___x_6687_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_wrapErasedDecl_spec__0___redArg();
return v___x_6687_;
}
else
{
lean_object* v_t_x3f_6688_; lean_object* v___x_6689_; 
v_t_x3f_6688_ = l_Lean_Syntax_getArg(v___x_6684_, v___x_6679_);
lean_dec(v___x_6684_);
v___x_6689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6689_, 0, v_t_x3f_6688_);
v_t_x3f_6634_ = v___x_6689_;
v___y_6635_ = v_a_6446_;
v___y_6636_ = v_a_6447_;
v___y_6637_ = v_a_6448_;
v___y_6638_ = v_a_6449_;
v___y_6639_ = v_a_6450_;
v___y_6640_ = v_a_6451_;
v___y_6641_ = v_a_6452_;
goto v___jp_6633_;
}
}
}
else
{
lean_object* v___x_6690_; 
lean_dec(v___x_6680_);
v___x_6690_ = lean_box(0);
v_t_x3f_6634_ = v___x_6690_;
v___y_6635_ = v_a_6446_;
v___y_6636_ = v_a_6447_;
v___y_6637_ = v_a_6448_;
v___y_6638_ = v_a_6449_;
v___y_6639_ = v_a_6450_;
v___y_6640_ = v_a_6451_;
v___y_6641_ = v_a_6452_;
goto v___jp_6633_;
}
}
v___jp_6592_:
{
lean_object* v___x_6602_; lean_object* v___x_6603_; 
v___x_6602_ = ((lean_object*)(l_Lean_Elab_Do_expandDoErasedArrow___closed__13));
v___x_6603_ = l_Lean_Core_mkFreshUserName(v___x_6602_, v___y_6600_, v___y_6601_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v_a_6604_; lean_object* v_ref_6605_; uint8_t v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; uint8_t v_kind_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; 
v_a_6604_ = lean_ctor_get(v___x_6603_, 0);
lean_inc(v_a_6604_);
lean_dec_ref_known(v___x_6603_, 1);
v_ref_6605_ = lean_ctor_get(v___y_6600_, 2);
v___x_6606_ = 0;
v___x_6607_ = l_Lean_mkIdentFrom(v_x_6591_, v_a_6604_, v___x_6606_);
v___x_6608_ = l_Lean_SourceInfo_fromRef(v_ref_6605_, v___x_6606_);
v___x_6609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassign___closed__1));
v___x_6610_ = ((lean_object*)(l_Lean_Elab_Do_elabDoErased___closed__4));
v___x_6611_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__41));
lean_inc_n(v___x_6608_, 4);
v___x_6612_ = l_Lean_Syntax_node1(v___x_6608_, v___x_6611_, v_x_6591_);
v___x_6613_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__12));
v___x_6614_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13, &l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__13);
v___x_6615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6615_, 0, v___x_6608_);
lean_ctor_set(v___x_6615_, 1, v___x_6613_);
lean_ctor_set(v___x_6615_, 2, v___x_6614_);
v___x_6616_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_pushTypeIntoReassignment___closed__14));
v___x_6617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6617_, 0, v___x_6608_);
lean_ctor_set(v___x_6617_, 1, v___x_6616_);
lean_inc(v___x_6607_);
lean_inc_ref(v___x_6615_);
v___x_6618_ = l_Lean_Syntax_node5(v___x_6608_, v___x_6610_, v___x_6612_, v___x_6615_, v___x_6615_, v___x_6617_, v___x_6607_);
v_kind_6619_ = lean_ctor_get_uint8(v_dec_6445_, sizeof(void*)*3);
v___x_6620_ = l_Lean_Syntax_node1(v___x_6608_, v___x_6609_, v___x_6618_);
v___x_6621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6621_, 0, v_t_6594_);
v___x_6622_ = lean_box(v___x_6455_);
v___x_6623_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoElem___boxed), 11, 3);
lean_closure_set(v___x_6623_, 0, v___x_6620_);
lean_closure_set(v___x_6623_, 1, v_dec_6445_);
lean_closure_set(v___x_6623_, 2, v___x_6622_);
v___x_6624_ = l_Lean_Elab_Do_elabDoIdDecl(v___x_6607_, v___x_6621_, v___y_6593_, v___x_6623_, v_kind_6619_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_);
return v___x_6624_;
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_dec(v_t_6594_);
lean_dec(v___y_6593_);
lean_dec(v_x_6591_);
lean_dec_ref(v_dec_6445_);
v_a_6625_ = lean_ctor_get(v___x_6603_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6603_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6603_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6630_; 
if (v_isShared_6628_ == 0)
{
v___x_6630_ = v___x_6627_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_a_6625_);
v___x_6630_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
return v___x_6630_;
}
}
}
}
v___jp_6633_:
{
lean_object* v___x_6642_; lean_object* v_rhs_6643_; lean_object* v___x_6644_; 
v___x_6642_ = lean_unsigned_to_nat(3u);
v_rhs_6643_ = l_Lean_Syntax_getArg(v___x_6458_, v___x_6642_);
lean_dec(v___x_6458_);
v___x_6644_ = l_Lean_Elab_Do_throwUnlessMutVarDeclared(v_x_6591_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
if (lean_obj_tag(v___x_6644_) == 0)
{
lean_dec_ref_known(v___x_6644_, 1);
if (lean_obj_tag(v_t_x3f_6634_) == 0)
{
lean_object* v___x_6645_; lean_object* v___x_6646_; 
v___x_6645_ = l_Lean_TSyntax_getId(v_x_6591_);
v___x_6646_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_6645_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
if (lean_obj_tag(v___x_6646_) == 0)
{
lean_object* v_a_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; 
v_a_6647_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_a_6647_);
lean_dec_ref_known(v___x_6646_, 1);
v___x_6648_ = l_Lean_LocalDecl_type(v_a_6647_);
lean_dec(v_a_6647_);
v___x_6649_ = l_Lean_Elab_Term_exprToSyntax(v___x_6648_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
if (lean_obj_tag(v___x_6649_) == 0)
{
lean_object* v_a_6650_; 
v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
lean_inc(v_a_6650_);
lean_dec_ref_known(v___x_6649_, 1);
v___y_6593_ = v_rhs_6643_;
v_t_6594_ = v_a_6650_;
v___y_6595_ = v___y_6635_;
v___y_6596_ = v___y_6636_;
v___y_6597_ = v___y_6637_;
v___y_6598_ = v___y_6638_;
v___y_6599_ = v___y_6639_;
v___y_6600_ = v___y_6640_;
v___y_6601_ = v___y_6641_;
goto v___jp_6592_;
}
else
{
lean_object* v_a_6651_; lean_object* v___x_6653_; uint8_t v_isShared_6654_; uint8_t v_isSharedCheck_6658_; 
lean_dec(v_rhs_6643_);
lean_dec(v_x_6591_);
lean_dec_ref(v_dec_6445_);
v_a_6651_ = lean_ctor_get(v___x_6649_, 0);
v_isSharedCheck_6658_ = !lean_is_exclusive(v___x_6649_);
if (v_isSharedCheck_6658_ == 0)
{
v___x_6653_ = v___x_6649_;
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
else
{
lean_inc(v_a_6651_);
lean_dec(v___x_6649_);
v___x_6653_ = lean_box(0);
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
v_resetjp_6652_:
{
lean_object* v___x_6656_; 
if (v_isShared_6654_ == 0)
{
v___x_6656_ = v___x_6653_;
goto v_reusejp_6655_;
}
else
{
lean_object* v_reuseFailAlloc_6657_; 
v_reuseFailAlloc_6657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6657_, 0, v_a_6651_);
v___x_6656_ = v_reuseFailAlloc_6657_;
goto v_reusejp_6655_;
}
v_reusejp_6655_:
{
return v___x_6656_;
}
}
}
}
else
{
lean_object* v_a_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6666_; 
lean_dec(v_rhs_6643_);
lean_dec(v_x_6591_);
lean_dec_ref(v_dec_6445_);
v_a_6659_ = lean_ctor_get(v___x_6646_, 0);
v_isSharedCheck_6666_ = !lean_is_exclusive(v___x_6646_);
if (v_isSharedCheck_6666_ == 0)
{
v___x_6661_ = v___x_6646_;
v_isShared_6662_ = v_isSharedCheck_6666_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_a_6659_);
lean_dec(v___x_6646_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6666_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
lean_object* v___x_6664_; 
if (v_isShared_6662_ == 0)
{
v___x_6664_ = v___x_6661_;
goto v_reusejp_6663_;
}
else
{
lean_object* v_reuseFailAlloc_6665_; 
v_reuseFailAlloc_6665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6665_, 0, v_a_6659_);
v___x_6664_ = v_reuseFailAlloc_6665_;
goto v_reusejp_6663_;
}
v_reusejp_6663_:
{
return v___x_6664_;
}
}
}
}
else
{
lean_object* v_val_6667_; 
v_val_6667_ = lean_ctor_get(v_t_x3f_6634_, 0);
lean_inc(v_val_6667_);
lean_dec_ref_known(v_t_x3f_6634_, 1);
v___y_6593_ = v_rhs_6643_;
v_t_6594_ = v_val_6667_;
v___y_6595_ = v___y_6635_;
v___y_6596_ = v___y_6636_;
v___y_6597_ = v___y_6637_;
v___y_6598_ = v___y_6638_;
v___y_6599_ = v___y_6639_;
v___y_6600_ = v___y_6640_;
v___y_6601_ = v___y_6641_;
goto v___jp_6592_;
}
}
else
{
lean_object* v_a_6668_; lean_object* v___x_6670_; uint8_t v_isShared_6671_; uint8_t v_isSharedCheck_6675_; 
lean_dec(v_rhs_6643_);
lean_dec(v_t_x3f_6634_);
lean_dec(v_x_6591_);
lean_dec_ref(v_dec_6445_);
v_a_6668_ = lean_ctor_get(v___x_6644_, 0);
v_isSharedCheck_6675_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6675_ == 0)
{
v___x_6670_ = v___x_6644_;
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
else
{
lean_inc(v_a_6668_);
lean_dec(v___x_6644_);
v___x_6670_ = lean_box(0);
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
v_resetjp_6669_:
{
lean_object* v___x_6673_; 
if (v_isShared_6671_ == 0)
{
v___x_6673_ = v___x_6670_;
goto v_reusejp_6672_;
}
else
{
lean_object* v_reuseFailAlloc_6674_; 
v_reuseFailAlloc_6674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6674_, 0, v_a_6668_);
v___x_6673_ = v_reuseFailAlloc_6674_;
goto v_reusejp_6672_;
}
v_reusejp_6672_:
{
return v___x_6673_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoReassignArrow___boxed(lean_object* v_stx_6691_, lean_object* v_dec_6692_, lean_object* v_a_6693_, lean_object* v_a_6694_, lean_object* v_a_6695_, lean_object* v_a_6696_, lean_object* v_a_6697_, lean_object* v_a_6698_, lean_object* v_a_6699_, lean_object* v_a_6700_){
_start:
{
lean_object* v_res_6701_; 
v_res_6701_ = l_Lean_Elab_Do_elabDoReassignArrow(v_stx_6691_, v_dec_6692_, v_a_6693_, v_a_6694_, v_a_6695_, v_a_6696_, v_a_6697_, v_a_6698_, v_a_6699_);
lean_dec(v_a_6699_);
lean_dec_ref(v_a_6698_);
lean_dec(v_a_6697_);
lean_dec_ref(v_a_6696_);
lean_dec(v_a_6695_);
lean_dec_ref(v_a_6694_);
lean_dec_ref(v_a_6693_);
return v_res_6701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1(){
_start:
{
lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; 
v___x_6709_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6710_ = ((lean_object*)(l_Lean_Elab_Do_elabDoReassignArrow___closed__1));
v___x_6711_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___closed__1));
v___x_6712_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoReassignArrow___boxed), 10, 0);
v___x_6713_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6709_, v___x_6710_, v___x_6711_, v___x_6712_);
return v___x_6713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1___boxed(lean_object* v_a_6714_){
_start:
{
lean_object* v_res_6715_; 
v_res_6715_ = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoReassignArrow___regBuiltin_Lean_Elab_Do_elabDoReassignArrow__1();
return v_res_6715_;
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
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_elabDoErased___regBuiltin_Lean_Elab_Do_elabDoErased__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Let_0__Lean_Elab_Do_expandDoErasedArrow___regBuiltin_Lean_Elab_Do_expandDoErasedArrow__1();
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
lean_object* runtime_initialize_Init_Data_Erased(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Erased(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Erased(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Let(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Erased(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
